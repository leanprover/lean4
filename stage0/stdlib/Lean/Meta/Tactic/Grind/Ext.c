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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_e_31_, v___y_39_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___boxed(lean_object* v_e_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3(v_e_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec(v___y_45_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(lean_object* v_k_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; 
lean_inc(v___y_63_);
lean_inc_ref(v___y_62_);
lean_inc(v___y_61_);
lean_inc_ref(v___y_60_);
lean_inc(v___y_59_);
lean_inc(v___y_58_);
v___x_69_ = lean_apply_11(v_k_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, lean_box(0));
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed(lean_object* v_k_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0(v_k_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec(v___y_71_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(lean_object* v_k_83_, uint8_t v_allowLevelAssignments_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___f_96_; lean_object* v___x_97_; 
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
lean_inc(v___y_86_);
lean_inc(v___y_85_);
v___f_96_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___lam__0___boxed), 12, 7);
lean_closure_set(v___f_96_, 0, v_k_83_);
lean_closure_set(v___f_96_, 1, v___y_85_);
lean_closure_set(v___f_96_, 2, v___y_86_);
lean_closure_set(v___f_96_, 3, v___y_87_);
lean_closure_set(v___f_96_, 4, v___y_88_);
lean_closure_set(v___f_96_, 5, v___y_89_);
lean_closure_set(v___f_96_, 6, v___y_90_);
v___x_97_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_84_, v___f_96_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
return v___x_97_;
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg___boxed(lean_object* v_k_106_, lean_object* v_allowLevelAssignments_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_119_; lean_object* v_res_120_; 
v_allowLevelAssignments_boxed_119_ = lean_unbox(v_allowLevelAssignments_107_);
v_res_120_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_106_, v_allowLevelAssignments_boxed_119_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec(v___y_108_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(lean_object* v_00_u03b1_121_, lean_object* v_k_122_, uint8_t v_allowLevelAssignments_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v_k_122_, v_allowLevelAssignments_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___boxed(lean_object* v_00_u03b1_136_, lean_object* v_k_137_, lean_object* v_allowLevelAssignments_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_150_; lean_object* v_res_151_; 
v_allowLevelAssignments_boxed_150_ = lean_unbox(v_allowLevelAssignments_138_);
v_res_151_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6(v_00_u03b1_136_, v_k_137_, v_allowLevelAssignments_boxed_150_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec(v___y_139_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_ks_156_; lean_object* v_vs_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_181_; 
v_ks_156_ = lean_ctor_get(v_x_152_, 0);
v_vs_157_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_181_ == 0)
{
v___x_159_ = v_x_152_;
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_vs_157_);
lean_inc(v_ks_156_);
lean_dec(v_x_152_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = lean_array_get_size(v_ks_156_);
v___x_162_ = lean_nat_dec_lt(v_x_153_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_x_153_);
v___x_163_ = lean_array_push(v_ks_156_, v_x_154_);
v___x_164_ = lean_array_push(v_vs_157_, v_x_155_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_164_);
lean_ctor_set(v___x_159_, 0, v___x_163_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_object* v_k_x27_168_; uint8_t v___x_169_; 
v_k_x27_168_ = lean_array_fget_borrowed(v_ks_156_, v_x_153_);
v___x_169_ = l_Lean_instBEqMVarId_beq(v_x_154_, v_k_x27_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_171_; 
if (v_isShared_160_ == 0)
{
v___x_171_ = v___x_159_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_ks_156_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_vs_157_);
v___x_171_ = v_reuseFailAlloc_175_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_add(v_x_153_, v___x_172_);
lean_dec(v_x_153_);
v_x_152_ = v___x_171_;
v_x_153_ = v___x_173_;
goto _start;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = lean_array_fset(v_ks_156_, v_x_153_, v_x_154_);
v___x_177_ = lean_array_fset(v_vs_157_, v_x_153_, v_x_155_);
lean_dec(v_x_153_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_177_);
lean_ctor_set(v___x_159_, 0, v___x_176_);
v___x_179_ = v___x_159_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(lean_object* v_n_182_, lean_object* v_k_183_, lean_object* v_v_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_n_182_, v___x_185_, v_k_183_, v_v_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(lean_object* v_x_188_, size_t v_x_189_, size_t v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_es_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v_j_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_es_193_ = lean_ctor_get(v_x_188_, 0);
v___x_194_ = ((size_t)31ULL);
v___x_195_ = lean_usize_land(v_x_189_, v___x_194_);
v_j_196_ = lean_usize_to_nat(v___x_195_);
v___x_197_ = lean_array_get_size(v_es_193_);
v___x_198_ = lean_nat_dec_lt(v_j_196_, v___x_197_);
if (v___x_198_ == 0)
{
lean_dec(v_j_196_);
lean_dec(v_x_192_);
lean_dec(v_x_191_);
return v_x_188_;
}
else
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_237_; 
lean_inc_ref(v_es_193_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_x_188_, 0);
lean_dec(v_unused_238_);
v___x_200_ = v_x_188_;
v_isShared_201_ = v_isSharedCheck_237_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_x_188_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_237_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v_v_202_; lean_object* v___x_203_; lean_object* v_xs_x27_204_; lean_object* v___y_206_; 
v_v_202_ = lean_array_fget(v_es_193_, v_j_196_);
v___x_203_ = lean_box(0);
v_xs_x27_204_ = lean_array_fset(v_es_193_, v_j_196_, v___x_203_);
switch(lean_obj_tag(v_v_202_))
{
case 0:
{
lean_object* v_key_211_; lean_object* v_val_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_222_; 
v_key_211_ = lean_ctor_get(v_v_202_, 0);
v_val_212_ = lean_ctor_get(v_v_202_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_v_202_);
if (v_isSharedCheck_222_ == 0)
{
v___x_214_ = v_v_202_;
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_val_212_);
lean_inc(v_key_211_);
lean_dec(v_v_202_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_222_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
uint8_t v___x_216_; 
v___x_216_ = l_Lean_instBEqMVarId_beq(v_x_191_, v_key_211_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_del_object(v___x_214_);
v___x_217_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_211_, v_val_212_, v_x_191_, v_x_192_);
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
v___y_206_ = v___x_218_;
goto v___jp_205_;
}
else
{
lean_object* v___x_220_; 
lean_dec(v_val_212_);
lean_dec(v_key_211_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v_x_192_);
lean_ctor_set(v___x_214_, 0, v_x_191_);
v___x_220_ = v___x_214_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_x_191_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_x_192_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
v___y_206_ = v___x_220_;
goto v___jp_205_;
}
}
}
}
case 1:
{
lean_object* v_node_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_235_; 
v_node_223_ = lean_ctor_get(v_v_202_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_v_202_);
if (v_isSharedCheck_235_ == 0)
{
v___x_225_ = v_v_202_;
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_node_223_);
lean_dec(v_v_202_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_227_ = ((size_t)5ULL);
v___x_228_ = lean_usize_shift_right(v_x_189_, v___x_227_);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_x_190_, v___x_229_);
v___x_231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_node_223_, v___x_228_, v___x_230_, v_x_191_, v_x_192_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_231_);
v___x_233_ = v___x_225_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v___y_206_ = v___x_233_;
goto v___jp_205_;
}
}
}
default: 
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_x_191_);
lean_ctor_set(v___x_236_, 1, v_x_192_);
v___y_206_ = v___x_236_;
goto v___jp_205_;
}
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_array_fset(v_xs_x27_204_, v_j_196_, v___y_206_);
lean_dec(v_j_196_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_207_);
v___x_209_ = v___x_200_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
else
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_260_; 
v_ks_239_ = lean_ctor_get(v_x_188_, 0);
v_vs_240_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_260_ == 0)
{
v___x_242_ = v_x_188_;
v_isShared_243_ = v_isSharedCheck_260_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_vs_240_);
lean_inc(v_ks_239_);
lean_dec(v_x_188_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_260_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_ks_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_vs_240_);
v___x_245_ = v_reuseFailAlloc_259_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v_newNode_246_; uint8_t v___y_248_; size_t v___x_254_; uint8_t v___x_255_; 
v_newNode_246_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v___x_245_, v_x_191_, v_x_192_);
v___x_254_ = ((size_t)7ULL);
v___x_255_ = lean_usize_dec_le(v___x_254_, v_x_190_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_246_);
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
lean_dec(v___x_256_);
v___y_248_ = v___x_258_;
goto v___jp_247_;
}
else
{
v___y_248_ = v___x_255_;
goto v___jp_247_;
}
v___jp_247_:
{
if (v___y_248_ == 0)
{
lean_object* v_ks_249_; lean_object* v_vs_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_ks_249_ = lean_ctor_get(v_newNode_246_, 0);
lean_inc_ref(v_ks_249_);
v_vs_250_ = lean_ctor_get(v_newNode_246_, 1);
lean_inc_ref(v_vs_250_);
lean_dec_ref(v_newNode_246_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_253_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_x_190_, v_ks_249_, v_vs_250_, v___x_251_, v___x_252_);
lean_dec_ref(v_vs_250_);
lean_dec_ref(v_ks_249_);
return v___x_253_;
}
else
{
return v_newNode_246_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(size_t v_depth_261_, lean_object* v_keys_262_, lean_object* v_vals_263_, lean_object* v_i_264_, lean_object* v_entries_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_keys_262_);
v___x_267_ = lean_nat_dec_lt(v_i_264_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_i_264_);
return v_entries_265_;
}
else
{
lean_object* v_k_268_; lean_object* v_v_269_; uint64_t v___x_270_; size_t v_h_271_; size_t v___x_272_; lean_object* v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v_h_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_k_268_ = lean_array_fget_borrowed(v_keys_262_, v_i_264_);
v_v_269_ = lean_array_fget_borrowed(v_vals_263_, v_i_264_);
v___x_270_ = l_Lean_instHashableMVarId_hash(v_k_268_);
v_h_271_ = lean_uint64_to_usize(v___x_270_);
v___x_272_ = ((size_t)5ULL);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_sub(v_depth_261_, v___x_274_);
v___x_276_ = lean_usize_mul(v___x_272_, v___x_275_);
v_h_277_ = lean_usize_shift_right(v_h_271_, v___x_276_);
v___x_278_ = lean_nat_add(v_i_264_, v___x_273_);
lean_dec(v_i_264_);
lean_inc(v_v_269_);
lean_inc(v_k_268_);
v___x_279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_entries_265_, v_h_277_, v_depth_261_, v_k_268_, v_v_269_);
v_i_264_ = v___x_278_;
v_entries_265_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg___boxed(lean_object* v_depth_281_, lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_entries_285_){
_start:
{
size_t v_depth_boxed_286_; lean_object* v_res_287_; 
v_depth_boxed_286_ = lean_unbox_usize(v_depth_281_);
lean_dec(v_depth_281_);
v_res_287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_boxed_286_, v_keys_282_, v_vals_283_, v_i_284_, v_entries_285_);
lean_dec_ref(v_vals_283_);
lean_dec_ref(v_keys_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
size_t v_x_214679__boxed_293_; size_t v_x_214680__boxed_294_; lean_object* v_res_295_; 
v_x_214679__boxed_293_ = lean_unbox_usize(v_x_289_);
lean_dec(v_x_289_);
v_x_214680__boxed_294_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_res_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_288_, v_x_214679__boxed_293_, v_x_214680__boxed_294_, v_x_291_, v_x_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint64_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_299_ = l_Lean_instHashableMVarId_hash(v_x_297_);
v___x_300_ = lean_uint64_to_usize(v___x_299_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_296_, v___x_300_, v___x_301_, v_x_297_, v_x_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(lean_object* v_mvarId_303_, lean_object* v_val_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_mctx_308_; lean_object* v_cache_309_; lean_object* v_zetaDeltaFVarIds_310_; lean_object* v_postponed_311_; lean_object* v_diag_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_340_; 
v___x_307_ = lean_st_ref_take(v___y_305_);
v_mctx_308_ = lean_ctor_get(v___x_307_, 0);
v_cache_309_ = lean_ctor_get(v___x_307_, 1);
v_zetaDeltaFVarIds_310_ = lean_ctor_get(v___x_307_, 2);
v_postponed_311_ = lean_ctor_get(v___x_307_, 3);
v_diag_312_ = lean_ctor_get(v___x_307_, 4);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_340_ == 0)
{
v___x_314_ = v___x_307_;
v_isShared_315_ = v_isSharedCheck_340_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_diag_312_);
lean_inc(v_postponed_311_);
lean_inc(v_zetaDeltaFVarIds_310_);
lean_inc(v_cache_309_);
lean_inc(v_mctx_308_);
lean_dec(v___x_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_340_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_depth_316_; lean_object* v_levelAssignDepth_317_; lean_object* v_lmvarCounter_318_; lean_object* v_mvarCounter_319_; lean_object* v_lDecls_320_; lean_object* v_decls_321_; lean_object* v_userNames_322_; lean_object* v_lAssignment_323_; lean_object* v_eAssignment_324_; lean_object* v_dAssignment_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_339_; 
v_depth_316_ = lean_ctor_get(v_mctx_308_, 0);
v_levelAssignDepth_317_ = lean_ctor_get(v_mctx_308_, 1);
v_lmvarCounter_318_ = lean_ctor_get(v_mctx_308_, 2);
v_mvarCounter_319_ = lean_ctor_get(v_mctx_308_, 3);
v_lDecls_320_ = lean_ctor_get(v_mctx_308_, 4);
v_decls_321_ = lean_ctor_get(v_mctx_308_, 5);
v_userNames_322_ = lean_ctor_get(v_mctx_308_, 6);
v_lAssignment_323_ = lean_ctor_get(v_mctx_308_, 7);
v_eAssignment_324_ = lean_ctor_get(v_mctx_308_, 8);
v_dAssignment_325_ = lean_ctor_get(v_mctx_308_, 9);
v_isSharedCheck_339_ = !lean_is_exclusive(v_mctx_308_);
if (v_isSharedCheck_339_ == 0)
{
v___x_327_ = v_mctx_308_;
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_dAssignment_325_);
lean_inc(v_eAssignment_324_);
lean_inc(v_lAssignment_323_);
lean_inc(v_userNames_322_);
lean_inc(v_decls_321_);
lean_inc(v_lDecls_320_);
lean_inc(v_mvarCounter_319_);
lean_inc(v_lmvarCounter_318_);
lean_inc(v_levelAssignDepth_317_);
lean_inc(v_depth_316_);
lean_dec(v_mctx_308_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_339_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_329_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_eAssignment_324_, v_mvarId_303_, v_val_304_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 8, v___x_329_);
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_depth_316_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_levelAssignDepth_317_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_lmvarCounter_318_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_mvarCounter_319_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_lDecls_320_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v_decls_321_);
lean_ctor_set(v_reuseFailAlloc_338_, 6, v_userNames_322_);
lean_ctor_set(v_reuseFailAlloc_338_, 7, v_lAssignment_323_);
lean_ctor_set(v_reuseFailAlloc_338_, 8, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_338_, 9, v_dAssignment_325_);
v___x_331_ = v_reuseFailAlloc_338_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_333_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_331_);
v___x_333_ = v___x_314_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_cache_309_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_zetaDeltaFVarIds_310_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_postponed_311_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_diag_312_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_st_ref_set(v___y_305_, v___x_333_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg___boxed(lean_object* v_mvarId_341_, lean_object* v_val_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_341_, v_val_342_, v___y_343_);
lean_dec(v___y_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(uint8_t v___x_346_, lean_object* v_p_347_, lean_object* v_e_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
uint8_t v___x_360_; 
v___x_360_ = l_Lean_Expr_isMVar(v_p_347_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_isExprDefEq(v_p_347_, v_e_348_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_371_; 
v___x_362_ = l_Lean_Expr_mvarId_x21(v_p_347_);
lean_dec_ref(v_p_347_);
v___x_363_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v___x_362_, v_e_348_, v___y_356_);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_372_);
v___x_365_ = v___x_363_;
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
else
{
lean_dec(v___x_363_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_box(v___x_346_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__0___boxed(lean_object* v___x_373_, lean_object* v_p_374_, lean_object* v_e_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v___x_214892__boxed_387_; lean_object* v_res_388_; 
v___x_214892__boxed_387_ = lean_unbox(v___x_373_);
v_res_388_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_214892__boxed_387_, v_p_374_, v_e_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec(v___y_376_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(lean_object* v_msgData_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v_env_396_; lean_object* v___x_397_; lean_object* v_mctx_398_; lean_object* v_lctx_399_; lean_object* v_options_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_395_ = lean_st_ref_get(v___y_393_);
v_env_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc_ref(v_env_396_);
lean_dec(v___x_395_);
v___x_397_ = lean_st_ref_get(v___y_391_);
v_mctx_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc_ref(v_mctx_398_);
lean_dec(v___x_397_);
v_lctx_399_ = lean_ctor_get(v___y_390_, 2);
v_options_400_ = lean_ctor_get(v___y_392_, 2);
lean_inc_ref(v_options_400_);
lean_inc_ref(v_lctx_399_);
v___x_401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_401_, 0, v_env_396_);
lean_ctor_set(v___x_401_, 1, v_mctx_398_);
lean_ctor_set(v___x_401_, 2, v_lctx_399_);
lean_ctor_set(v___x_401_, 3, v_options_400_);
v___x_402_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v_msgData_389_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6___boxed(lean_object* v_msgData_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msgData_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_411_; double v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_float_of_nat(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(lean_object* v_cls_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_ref_423_; lean_object* v___x_424_; lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_469_; 
v_ref_423_ = lean_ctor_get(v___y_420_, 5);
v___x_424_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4_spec__6(v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_469_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_469_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_469_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v_traceState_430_; lean_object* v_env_431_; lean_object* v_nextMacroScope_432_; lean_object* v_ngen_433_; lean_object* v_auxDeclNGen_434_; lean_object* v_cache_435_; lean_object* v_messages_436_; lean_object* v_infoState_437_; lean_object* v_snapshotTasks_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_468_; 
v___x_429_ = lean_st_ref_take(v___y_421_);
v_traceState_430_ = lean_ctor_get(v___x_429_, 4);
v_env_431_ = lean_ctor_get(v___x_429_, 0);
v_nextMacroScope_432_ = lean_ctor_get(v___x_429_, 1);
v_ngen_433_ = lean_ctor_get(v___x_429_, 2);
v_auxDeclNGen_434_ = lean_ctor_get(v___x_429_, 3);
v_cache_435_ = lean_ctor_get(v___x_429_, 5);
v_messages_436_ = lean_ctor_get(v___x_429_, 6);
v_infoState_437_ = lean_ctor_get(v___x_429_, 7);
v_snapshotTasks_438_ = lean_ctor_get(v___x_429_, 8);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_468_ == 0)
{
v___x_440_ = v___x_429_;
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snapshotTasks_438_);
lean_inc(v_infoState_437_);
lean_inc(v_messages_436_);
lean_inc(v_cache_435_);
lean_inc(v_traceState_430_);
lean_inc(v_auxDeclNGen_434_);
lean_inc(v_ngen_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_env_431_);
lean_dec(v___x_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint64_t v_tid_442_; lean_object* v_traces_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_467_; 
v_tid_442_ = lean_ctor_get_uint64(v_traceState_430_, sizeof(void*)*1);
v_traces_443_ = lean_ctor_get(v_traceState_430_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v_traceState_430_);
if (v_isSharedCheck_467_ == 0)
{
v___x_445_ = v_traceState_430_;
v_isShared_446_ = v_isSharedCheck_467_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_traces_443_);
lean_dec(v_traceState_430_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_467_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; double v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_447_ = lean_box(0);
v___x_448_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__0);
v___x_449_ = 0;
v___x_450_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__1));
v___x_451_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_451_, 0, v_cls_416_);
lean_ctor_set(v___x_451_, 1, v___x_447_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
lean_ctor_set_float(v___x_451_, sizeof(void*)*3, v___x_448_);
lean_ctor_set_float(v___x_451_, sizeof(void*)*3 + 8, v___x_448_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*3 + 16, v___x_449_);
v___x_452_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___closed__2));
v___x_453_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v_a_425_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
lean_inc(v_ref_423_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_ref_423_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_PersistentArray_push___redArg(v_traces_443_, v___x_454_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_455_);
v___x_457_ = v___x_445_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_455_);
lean_ctor_set_uint64(v_reuseFailAlloc_466_, sizeof(void*)*1, v_tid_442_);
v___x_457_ = v_reuseFailAlloc_466_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 4, v___x_457_);
v___x_459_ = v___x_440_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_env_431_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_ngen_433_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_auxDeclNGen_434_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_messages_436_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_infoState_437_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_snapshotTasks_438_);
v___x_459_ = v_reuseFailAlloc_465_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_460_ = lean_st_ref_set(v___y_421_, v___x_459_);
v___x_461_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_461_);
v___x_463_ = v___x_427_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg___boxed(lean_object* v_cls_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_470_, v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_477_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(lean_object* v_keys_478_, lean_object* v_i_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_array_get_size(v_keys_478_);
v___x_482_ = lean_nat_dec_lt(v_i_479_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v_i_479_);
return v___x_482_;
}
else
{
lean_object* v_k_x27_483_; uint8_t v___x_484_; 
v_k_x27_483_ = lean_array_fget_borrowed(v_keys_478_, v_i_479_);
v___x_484_ = l_Lean_instBEqMVarId_beq(v_k_480_, v_k_x27_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_i_479_, v___x_485_);
lean_dec(v_i_479_);
v_i_479_ = v___x_486_;
goto _start;
}
else
{
lean_dec(v_i_479_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg___boxed(lean_object* v_keys_488_, lean_object* v_i_489_, lean_object* v_k_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_488_, v_i_489_, v_k_490_);
lean_dec(v_k_490_);
lean_dec_ref(v_keys_488_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(lean_object* v_x_493_, size_t v_x_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v_es_496_; lean_object* v___x_497_; size_t v___x_498_; size_t v___x_499_; lean_object* v_j_500_; lean_object* v___x_501_; 
v_es_496_ = lean_ctor_get(v_x_493_, 0);
v___x_497_ = lean_box(2);
v___x_498_ = ((size_t)31ULL);
v___x_499_ = lean_usize_land(v_x_494_, v___x_498_);
v_j_500_ = lean_usize_to_nat(v___x_499_);
v___x_501_ = lean_array_get_borrowed(v___x_497_, v_es_496_, v_j_500_);
lean_dec(v_j_500_);
switch(lean_obj_tag(v___x_501_))
{
case 0:
{
lean_object* v_key_502_; uint8_t v___x_503_; 
v_key_502_ = lean_ctor_get(v___x_501_, 0);
v___x_503_ = l_Lean_instBEqMVarId_beq(v_x_495_, v_key_502_);
return v___x_503_;
}
case 1:
{
lean_object* v_node_504_; size_t v___x_505_; size_t v___x_506_; 
v_node_504_ = lean_ctor_get(v___x_501_, 0);
v___x_505_ = ((size_t)5ULL);
v___x_506_ = lean_usize_shift_right(v_x_494_, v___x_505_);
v_x_493_ = v_node_504_;
v_x_494_ = v___x_506_;
goto _start;
}
default: 
{
uint8_t v___x_508_; 
v___x_508_ = 0;
return v___x_508_;
}
}
}
else
{
lean_object* v_ks_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
v_ks_509_ = lean_ctor_get(v_x_493_, 0);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_ks_509_, v___x_510_, v_x_495_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
size_t v_x_215095__boxed_515_; uint8_t v_res_516_; lean_object* v_r_517_; 
v_x_215095__boxed_515_ = lean_unbox_usize(v_x_513_);
lean_dec(v_x_513_);
v_res_516_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_512_, v_x_215095__boxed_515_, v_x_514_);
lean_dec(v_x_514_);
lean_dec_ref(v_x_512_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
uint64_t v___x_520_; size_t v___x_521_; uint8_t v___x_522_; 
v___x_520_ = l_Lean_instHashableMVarId_hash(v_x_519_);
v___x_521_ = lean_uint64_to_usize(v___x_520_);
v___x_522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_518_, v___x_521_, v_x_519_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg___boxed(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_523_, v_x_524_);
lean_dec(v_x_524_);
lean_dec_ref(v_x_523_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(lean_object* v_mvarId_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v_mctx_531_; lean_object* v_eAssignment_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_530_ = lean_st_ref_get(v___y_528_);
v_mctx_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_mctx_531_);
lean_dec(v___x_530_);
v_eAssignment_532_ = lean_ctor_get(v_mctx_531_, 8);
lean_inc_ref(v_eAssignment_532_);
lean_dec_ref(v_mctx_531_);
v___x_533_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_eAssignment_532_, v_mvarId_527_);
lean_dec_ref(v_eAssignment_532_);
v___x_534_ = lean_box(v___x_533_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg___boxed(lean_object* v_mvarId_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec(v_mvarId_536_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(lean_object* v_as_540_, size_t v_i_541_, size_t v_stop_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_a_556_; uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_eq(v_i_541_, v_stop_542_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; uint8_t v_a_563_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_561_ = lean_array_uget_borrowed(v_as_540_, v_i_541_);
v___x_565_ = l_Lean_Expr_mvarId_x21(v___x_561_);
v___x_566_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_565_, v___y_551_);
lean_dec(v___x_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; uint8_t v___x_568_; uint8_t v___x_569_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = lean_unbox(v_a_567_);
lean_dec(v_a_567_);
v___x_569_ = lean_bool_not(v___x_568_);
v_a_563_ = v___x_569_;
goto v___jp_562_;
}
else
{
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_570_; uint8_t v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_566_, 1);
v___x_571_ = lean_unbox(v_a_570_);
lean_dec(v_a_570_);
v_a_563_ = v___x_571_;
goto v___jp_562_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_dec_ref(v_b_543_);
v_a_572_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_566_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_566_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
v___jp_562_:
{
if (v_a_563_ == 0)
{
v_a_556_ = v_b_543_;
goto v___jp_555_;
}
else
{
lean_object* v___x_564_; 
lean_inc(v___x_561_);
v___x_564_ = lean_array_push(v_b_543_, v___x_561_);
v_a_556_ = v___x_564_;
goto v___jp_555_;
}
}
}
else
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v_b_543_);
return v___x_580_;
}
v___jp_555_:
{
size_t v___x_557_; size_t v___x_558_; 
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_541_, v___x_557_);
v_i_541_ = v___x_558_;
v_b_543_ = v_a_556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5___boxed(lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
size_t v_i_boxed_596_; size_t v_stop_boxed_597_; lean_object* v_res_598_; 
v_i_boxed_596_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_597_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v_as_581_, v_i_boxed_596_, v_stop_boxed_597_, v_b_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v_as_581_);
return v_res_598_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__1));
v___x_603_ = l_Lean_stringToMessageData(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__3));
v___x_606_ = l_Lean_stringToMessageData(v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(lean_object* v___x_607_, lean_object* v_e_608_, lean_object* v_as_609_, size_t v_sz_610_, size_t v_i_611_, lean_object* v_b_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_a_625_; uint8_t v___x_629_; 
v___x_629_ = lean_usize_dec_lt(v_i_611_, v_sz_610_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v_b_612_);
return v___x_630_;
}
else
{
lean_object* v_snd_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_737_; 
v_snd_631_ = lean_ctor_get(v_b_612_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_b_612_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_b_612_, 0);
lean_dec(v_unused_738_);
v___x_633_ = v_b_612_;
v_isShared_634_ = v_isSharedCheck_737_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snd_631_);
lean_dec(v_b_612_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_737_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v_array_635_; lean_object* v_start_636_; lean_object* v_stop_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_array_635_ = lean_ctor_get(v_snd_631_, 0);
v_start_636_ = lean_ctor_get(v_snd_631_, 1);
v_stop_637_ = lean_ctor_get(v_snd_631_, 2);
v___x_638_ = lean_box(0);
v___x_639_ = lean_nat_dec_lt(v_start_636_, v_stop_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_638_);
v___x_641_ = v___x_633_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_snd_631_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
else
{
lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_733_; 
lean_inc(v_stop_637_);
lean_inc(v_start_636_);
lean_inc_ref(v_array_635_);
v_isSharedCheck_733_ = !lean_is_exclusive(v_snd_631_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_734_ = lean_ctor_get(v_snd_631_, 2);
lean_dec(v_unused_734_);
v_unused_735_ = lean_ctor_get(v_snd_631_, 1);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_snd_631_, 0);
lean_dec(v_unused_736_);
v___x_645_ = v_snd_631_;
v_isShared_646_ = v_isSharedCheck_733_;
goto v_resetjp_644_;
}
else
{
lean_dec(v_snd_631_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_733_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v_a_647_ = lean_array_uget_borrowed(v_as_609_, v_i_611_);
v___x_648_ = l_Lean_Expr_mvarId_x21(v_a_647_);
v___x_649_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v___x_648_, v___y_620_);
lean_dec(v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_724_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_724_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_724_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_724_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_654_ = lean_array_fget(v_array_635_, v_start_636_);
v___x_655_ = lean_unsigned_to_nat(1u);
v___x_656_ = lean_nat_add(v_start_636_, v___x_655_);
lean_dec(v_start_636_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_656_);
v___x_658_ = v___x_645_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_array_635_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v_stop_637_);
v___x_658_ = v_reuseFailAlloc_723_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
uint8_t v___y_668_; uint8_t v___x_719_; uint8_t v___x_720_; 
v___x_719_ = lean_unbox(v___x_654_);
lean_dec(v___x_654_);
v___x_720_ = l_Lean_BinderInfo_isInstImplicit(v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v_a_650_);
v___y_668_ = v___x_720_;
goto v___jp_667_;
}
else
{
uint8_t v___x_721_; uint8_t v___x_722_; 
v___x_721_ = lean_unbox(v_a_650_);
lean_dec(v_a_650_);
v___x_722_ = lean_bool_not(v___x_721_);
v___y_668_ = v___x_722_;
goto v___jp_667_;
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__0));
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_658_);
lean_ctor_set(v___x_633_, 0, v___x_660_);
v___x_662_ = v___x_633_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_658_);
v___x_662_ = v_reuseFailAlloc_666_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_662_);
v___x_664_ = v___x_652_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
lean_object* v___x_669_; 
lean_del_object(v___x_652_);
lean_del_object(v___x_633_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_638_);
lean_ctor_set(v___x_669_, 1, v___x_658_);
v_a_625_ = v___x_669_;
goto v___jp_624_;
}
else
{
lean_object* v___x_670_; 
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v_a_647_);
v___x_670_ = lean_infer_type(v_a_647_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
lean_inc(v_a_647_);
v___x_672_ = l_Lean_Meta_Sym_synthInstanceAndAssign___redArg(v_a_647_, v_a_671_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; uint8_t v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = lean_unbox(v_a_673_);
lean_dec(v_a_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_617_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; uint8_t v_verbose_677_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v_verbose_677_ = lean_ctor_get_uint8(v_a_676_, 0);
lean_dec(v_a_676_);
if (v_verbose_677_ == 0)
{
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
goto v___jp_659_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_678_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__2);
v___x_679_ = l_Lean_MessageData_ofName(v___x_607_);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_Lean_indentExpr(v_e_608_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_Meta_Sym_reportIssue(v___x_684_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_dec_ref_known(v___x_685_, 1);
goto v___jp_659_;
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v___x_658_);
lean_del_object(v___x_652_);
lean_del_object(v___x_633_);
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v___x_658_);
lean_del_object(v___x_652_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
v_a_694_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_675_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_675_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_object* v___x_702_; 
lean_del_object(v___x_652_);
lean_del_object(v___x_633_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_638_);
lean_ctor_set(v___x_702_, 1, v___x_658_);
v_a_625_ = v___x_702_;
goto v___jp_624_;
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v___x_658_);
lean_del_object(v___x_652_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
v_a_703_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_672_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_672_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___x_658_);
lean_del_object(v___x_652_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
v_a_711_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_670_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_670_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
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
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_645_);
lean_dec(v_stop_637_);
lean_dec(v_start_636_);
lean_dec_ref(v_array_635_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_608_);
lean_dec(v___x_607_);
v_a_725_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_649_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_649_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
v___jp_624_:
{
size_t v___x_626_; size_t v___x_627_; 
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_add(v_i_611_, v___x_626_);
v_i_611_ = v___x_627_;
v_b_612_ = v_a_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___boxed(lean_object** _args){
lean_object* v___x_739_ = _args[0];
lean_object* v_e_740_ = _args[1];
lean_object* v_as_741_ = _args[2];
lean_object* v_sz_742_ = _args[3];
lean_object* v_i_743_ = _args[4];
lean_object* v_b_744_ = _args[5];
lean_object* v___y_745_ = _args[6];
lean_object* v___y_746_ = _args[7];
lean_object* v___y_747_ = _args[8];
lean_object* v___y_748_ = _args[9];
lean_object* v___y_749_ = _args[10];
lean_object* v___y_750_ = _args[11];
lean_object* v___y_751_ = _args[12];
lean_object* v___y_752_ = _args[13];
lean_object* v___y_753_ = _args[14];
lean_object* v___y_754_ = _args[15];
lean_object* v___y_755_ = _args[16];
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_742_);
lean_dec(v_sz_742_);
v_i_boxed_757_ = lean_unbox_usize(v_i_743_);
lean_dec(v_i_743_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v___x_739_, v_e_740_, v_as_741_, v_sz_boxed_756_, v_i_boxed_757_, v_b_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v_as_741_);
return v_res_758_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_771_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__6));
v___x_772_ = l_Lean_Name_append(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__8));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__10));
v___x_778_ = l_Lean_stringToMessageData(v___x_777_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__12));
v___x_781_ = l_Lean_stringToMessageData(v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__14));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__18));
v___x_793_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__17));
v___x_794_ = l_Lean_mkConst(v___x_793_, v___x_792_);
return v___x_794_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21(void){
_start:
{
uint8_t v___x_797_; uint64_t v___x_798_; 
v___x_797_ = 1;
v___x_798_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(lean_object* v_e_799_, lean_object* v_thm_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_799_, v___y_801_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = l_Lean_Meta_Grind_getMaxGeneration___redArg(v___y_803_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_1167_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_1167_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_1167_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v___x_831_; 
v___x_831_ = lean_nat_dec_lt(v_a_825_, v_a_827_);
lean_dec(v_a_827_);
lean_dec(v_a_825_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
v___x_832_ = lean_box(0);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_832_);
v___x_834_ = v___x_829_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v___x_836_; uint8_t v___x_837_; 
lean_del_object(v___x_829_);
lean_inc_ref(v_e_799_);
v___x_836_ = l_Lean_Expr_cleanupAnnotations(v_e_799_);
v___x_837_ = l_Lean_Expr_isApp(v___x_836_);
if (v___x_837_ == 0)
{
lean_dec_ref(v___x_836_);
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
goto v___jp_821_;
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
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
goto v___jp_821_;
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
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
goto v___jp_821_;
}
else
{
lean_object* v_arg_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_arg_844_ = lean_ctor_get(v___x_842_, 1);
lean_inc_ref(v_arg_844_);
v___x_845_ = l_Lean_Expr_appFnCleanup___redArg(v___x_842_);
v___x_846_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__1));
v___x_847_ = l_Lean_Expr_isConstOf(v___x_845_, v___x_846_);
lean_dec_ref(v___x_845_);
if (v___x_847_ == 0)
{
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
goto v___jp_821_;
}
else
{
lean_object* v_declName_848_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_878_; lean_object* v___y_879_; uint8_t v___y_880_; lean_object* v___y_915_; uint8_t v___y_916_; lean_object* v_a_917_; lean_object* v___y_945_; uint8_t v___y_946_; lean_object* v___y_947_; lean_object* v___y_958_; lean_object* v___x_982_; 
v_declName_848_ = lean_ctor_get(v_thm_800_, 0);
lean_inc_n(v_declName_848_, 2);
lean_dec_ref(v_thm_800_);
v___x_982_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_declName_848_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___y_985_; lean_object* v___y_986_; uint8_t v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v_a_1060_; lean_object* v___x_1091_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_n(v_a_983_, 2);
lean_dec_ref_known(v___x_982_, 1);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
v___x_1091_ = lean_infer_type(v_a_983_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; uint8_t v_foApprox_1094_; uint8_t v_ctxApprox_1095_; uint8_t v_quasiPatternApprox_1096_; uint8_t v_constApprox_1097_; uint8_t v_isDefEqStuckEx_1098_; uint8_t v_unificationHints_1099_; uint8_t v_proofIrrelevance_1100_; uint8_t v_assignSyntheticOpaque_1101_; uint8_t v_offsetCnstrs_1102_; uint8_t v_etaStruct_1103_; uint8_t v_univApprox_1104_; uint8_t v_iota_1105_; uint8_t v_beta_1106_; uint8_t v_proj_1107_; uint8_t v_zeta_1108_; uint8_t v_zetaDelta_1109_; uint8_t v_zetaUnused_1110_; uint8_t v_zetaHave_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1150_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = l_Lean_Meta_Context_config(v___y_807_);
v_foApprox_1094_ = lean_ctor_get_uint8(v___x_1093_, 0);
v_ctxApprox_1095_ = lean_ctor_get_uint8(v___x_1093_, 1);
v_quasiPatternApprox_1096_ = lean_ctor_get_uint8(v___x_1093_, 2);
v_constApprox_1097_ = lean_ctor_get_uint8(v___x_1093_, 3);
v_isDefEqStuckEx_1098_ = lean_ctor_get_uint8(v___x_1093_, 4);
v_unificationHints_1099_ = lean_ctor_get_uint8(v___x_1093_, 5);
v_proofIrrelevance_1100_ = lean_ctor_get_uint8(v___x_1093_, 6);
v_assignSyntheticOpaque_1101_ = lean_ctor_get_uint8(v___x_1093_, 7);
v_offsetCnstrs_1102_ = lean_ctor_get_uint8(v___x_1093_, 8);
v_etaStruct_1103_ = lean_ctor_get_uint8(v___x_1093_, 10);
v_univApprox_1104_ = lean_ctor_get_uint8(v___x_1093_, 11);
v_iota_1105_ = lean_ctor_get_uint8(v___x_1093_, 12);
v_beta_1106_ = lean_ctor_get_uint8(v___x_1093_, 13);
v_proj_1107_ = lean_ctor_get_uint8(v___x_1093_, 14);
v_zeta_1108_ = lean_ctor_get_uint8(v___x_1093_, 15);
v_zetaDelta_1109_ = lean_ctor_get_uint8(v___x_1093_, 16);
v_zetaUnused_1110_ = lean_ctor_get_uint8(v___x_1093_, 17);
v_zetaHave_1111_ = lean_ctor_get_uint8(v___x_1093_, 18);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1113_ = v___x_1093_;
v_isShared_1114_ = v_isSharedCheck_1150_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v___x_1093_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1150_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
uint8_t v_trackZetaDelta_1115_; lean_object* v_zetaDeltaSet_1116_; lean_object* v_lctx_1117_; lean_object* v_localInstances_1118_; lean_object* v_defEqCtx_x3f_1119_; lean_object* v_synthPendingDepth_1120_; lean_object* v_canUnfold_x3f_1121_; uint8_t v_univApprox_1122_; uint8_t v_inTypeClassResolution_1123_; uint8_t v_cacheInferType_1124_; uint8_t v___x_1125_; lean_object* v_config_1127_; 
v_trackZetaDelta_1115_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*7);
v_zetaDeltaSet_1116_ = lean_ctor_get(v___y_807_, 1);
v_lctx_1117_ = lean_ctor_get(v___y_807_, 2);
v_localInstances_1118_ = lean_ctor_get(v___y_807_, 3);
v_defEqCtx_x3f_1119_ = lean_ctor_get(v___y_807_, 4);
v_synthPendingDepth_1120_ = lean_ctor_get(v___y_807_, 5);
v_canUnfold_x3f_1121_ = lean_ctor_get(v___y_807_, 6);
v_univApprox_1122_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1123_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*7 + 2);
v_cacheInferType_1124_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*7 + 3);
v___x_1125_ = 1;
if (v_isShared_1114_ == 0)
{
v_config_1127_ = v___x_1113_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 0, v_foApprox_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 1, v_ctxApprox_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 2, v_quasiPatternApprox_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 3, v_constApprox_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 4, v_isDefEqStuckEx_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 5, v_unificationHints_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 6, v_proofIrrelevance_1100_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 7, v_assignSyntheticOpaque_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 8, v_offsetCnstrs_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 10, v_etaStruct_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 11, v_univApprox_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 12, v_iota_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 13, v_beta_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 14, v_proj_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 15, v_zeta_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 16, v_zetaDelta_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 17, v_zetaUnused_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1149_, 18, v_zetaHave_1111_);
v_config_1127_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
uint64_t v___x_1128_; uint64_t v___x_1129_; uint64_t v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; uint64_t v___x_1133_; uint64_t v___x_1134_; uint64_t v_key_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_ctor_set_uint8(v_config_1127_, 9, v___x_1125_);
v___x_1128_ = l_Lean_Meta_Context_configKey(v___y_807_);
v___x_1129_ = 3ULL;
v___x_1130_ = lean_uint64_shift_right(v___x_1128_, v___x_1129_);
v___x_1131_ = lean_box(0);
v___x_1132_ = 0;
v___x_1133_ = lean_uint64_shift_left(v___x_1130_, v___x_1129_);
v___x_1134_ = lean_uint64_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__21);
v_key_1135_ = lean_uint64_lor(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1136_, 0, v_config_1127_);
lean_ctor_set_uint64(v___x_1136_, sizeof(void*)*1, v_key_1135_);
lean_inc(v_canUnfold_x3f_1121_);
lean_inc(v_synthPendingDepth_1120_);
lean_inc(v_defEqCtx_x3f_1119_);
lean_inc_ref(v_localInstances_1118_);
lean_inc_ref(v_lctx_1117_);
lean_inc(v_zetaDeltaSet_1116_);
v___x_1137_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_zetaDeltaSet_1116_);
lean_ctor_set(v___x_1137_, 2, v_lctx_1117_);
lean_ctor_set(v___x_1137_, 3, v_localInstances_1118_);
lean_ctor_set(v___x_1137_, 4, v_defEqCtx_x3f_1119_);
lean_ctor_set(v___x_1137_, 5, v_synthPendingDepth_1120_);
lean_ctor_set(v___x_1137_, 6, v_canUnfold_x3f_1121_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7, v_trackZetaDelta_1115_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7 + 1, v_univApprox_1122_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1123_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*7 + 3, v_cacheInferType_1124_);
v___x_1138_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1092_, v___x_1131_, v___x_1132_, v___x_1137_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref_known(v___x_1137_, 7);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v_a_1060_ = v_a_1139_;
goto v___jp_1059_;
}
else
{
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1138_, 1);
v_a_1060_ = v_a_1140_;
goto v___jp_1059_;
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
v_a_1141_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1138_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1138_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
v_a_1151_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1091_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1091_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
v___jp_984_:
{
if (lean_obj_tag(v___y_989_) == 0)
{
lean_object* v_a_990_; uint8_t v___x_991_; 
v_a_990_ = lean_ctor_get(v___y_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___y_989_, 1);
v___x_991_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v_a_983_);
v___y_958_ = v___y_988_;
goto v___jp_957_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; size_t v_sz_997_; size_t v___x_998_; lean_object* v___x_999_; 
lean_dec_ref(v___y_988_);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_array_get_size(v___y_986_);
v___x_994_ = l_Array_toSubarray___redArg(v___y_986_, v___x_992_, v___x_993_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
v_sz_997_ = lean_array_size(v___y_985_);
v___x_998_ = ((size_t)0ULL);
lean_inc_ref(v_e_799_);
lean_inc(v_declName_848_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2(v_declName_848_, v_e_799_, v___y_985_, v_sz_997_, v___x_998_, v___x_996_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1042_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1042_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1042_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_fst_1004_; 
v_fst_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_fst_1004_);
lean_dec(v_a_1000_);
if (lean_obj_tag(v_fst_1004_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_a_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_1002_);
v___x_1005_ = l_Lean_mkAppN(v_a_983_, v___y_985_);
v___x_1006_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v___x_1005_, v___y_808_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v___x_1006_);
lean_inc_ref(v_e_799_);
v___x_1008_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_799_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_805_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_a_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v___x_1012_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__19);
lean_inc_ref(v_e_799_);
v___x_1013_ = l_Lean_mkApp4(v___x_1012_, v_e_799_, v_a_1011_, v_a_1009_, v_a_1007_);
v___x_1014_ = lean_array_get_size(v___y_985_);
v___x_1015_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__20));
v___x_1016_ = lean_nat_dec_lt(v___x_992_, v___x_1014_);
if (v___x_1016_ == 0)
{
lean_dec_ref(v___y_985_);
v___y_915_ = v___x_1013_;
v___y_916_ = v___y_987_;
v_a_917_ = v___x_1015_;
goto v___jp_914_;
}
else
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_nat_dec_le(v___x_1014_, v___x_1014_);
if (v___x_1017_ == 0)
{
if (v___x_1016_ == 0)
{
lean_dec_ref(v___y_985_);
v___y_915_ = v___x_1013_;
v___y_916_ = v___y_987_;
v_a_917_ = v___x_1015_;
goto v___jp_914_;
}
else
{
size_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_usize_of_nat(v___x_1014_);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_985_, v___x_998_, v___x_1018_, v___x_1015_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v___y_985_);
v___y_945_ = v___x_1013_;
v___y_946_ = v___y_987_;
v___y_947_ = v___x_1019_;
goto v___jp_944_;
}
}
else
{
size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_usize_of_nat(v___x_1014_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__5(v___y_985_, v___x_998_, v___x_1020_, v___x_1015_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v___y_985_);
v___y_945_ = v___x_1013_;
v___y_946_ = v___y_987_;
v___y_947_ = v___x_1021_;
goto v___jp_944_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_a_1009_);
lean_dec(v_a_1007_);
lean_dec_ref(v___y_985_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_1022_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1010_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1010_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec(v_a_1007_);
lean_dec_ref(v___y_985_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_1030_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1008_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1008_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1040_; 
lean_dec_ref(v___y_985_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_val_1038_ = lean_ctor_get(v_fst_1004_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v_fst_1004_, 1);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_val_1038_);
v___x_1040_ = v___x_1002_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_val_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v___y_985_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_1043_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_999_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_999_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v___y_988_);
lean_dec_ref(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_1051_ = lean_ctor_get(v___y_989_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___y_989_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___y_989_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___y_989_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
v___jp_1059_:
{
lean_object* v_snd_1061_; lean_object* v_fst_1062_; lean_object* v_fst_1063_; lean_object* v_snd_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_snd_1061_ = lean_ctor_get(v_a_1060_, 1);
lean_inc(v_snd_1061_);
v_fst_1062_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_fst_1062_);
lean_dec_ref(v_a_1060_);
v_fst_1063_ = lean_ctor_get(v_snd_1061_, 0);
lean_inc(v_fst_1063_);
v_snd_1064_ = lean_ctor_get(v_snd_1061_, 1);
lean_inc_n(v_snd_1064_, 2);
lean_dec(v_snd_1061_);
v___x_1065_ = l_Lean_Expr_cleanupAnnotations(v_snd_1064_);
v___x_1066_ = l_Lean_Expr_isApp(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v___x_1065_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1062_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
goto v___jp_818_;
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
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1062_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
goto v___jp_818_;
}
else
{
lean_object* v_arg_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_arg_1070_ = lean_ctor_get(v___x_1068_, 1);
lean_inc_ref(v_arg_1070_);
v___x_1071_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1068_);
v___x_1072_ = l_Lean_Expr_isApp(v___x_1071_);
if (v___x_1072_ == 0)
{
lean_dec_ref(v___x_1071_);
lean_dec_ref(v_arg_1070_);
lean_dec_ref(v_arg_1067_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1062_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
goto v___jp_818_;
}
else
{
lean_object* v_arg_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v_arg_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc_ref(v_arg_1073_);
v___x_1074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1071_);
v___x_1075_ = l_Lean_Expr_isConstOf(v___x_1074_, v___x_846_);
lean_dec_ref(v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec_ref(v_arg_1073_);
lean_dec_ref(v_arg_1070_);
lean_dec_ref(v_arg_1067_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1062_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
goto v___jp_818_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Meta_isExprDefEq(v_arg_844_, v_arg_1073_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; uint8_t v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
v___x_1078_ = lean_unbox(v_a_1077_);
lean_dec(v_a_1077_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v_arg_1070_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
v___y_985_ = v_fst_1062_;
v___y_986_ = v_fst_1063_;
v___y_987_ = v___x_1075_;
v___y_988_ = v_snd_1064_;
v___y_989_ = v___x_1076_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1079_; 
lean_dec_ref_known(v___x_1076_, 1);
v___x_1079_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1075_, v_arg_1070_, v_arg_841_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; uint8_t v___x_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_unbox(v_a_1080_);
lean_dec(v_a_1080_);
if (v___x_1081_ == 0)
{
lean_dec_ref(v_arg_1067_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1062_);
lean_dec(v_a_983_);
lean_dec_ref(v_arg_838_);
v___y_958_ = v_snd_1064_;
goto v___jp_957_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__0(v___x_1075_, v_arg_1067_, v_arg_838_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
v___y_985_ = v_fst_1062_;
v___y_986_ = v_fst_1063_;
v___y_987_ = v___x_1075_;
v___y_988_ = v_snd_1064_;
v___y_989_ = v___x_1082_;
goto v___jp_984_;
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_arg_1067_);
lean_dec(v_snd_1064_);
lean_dec(v_fst_1063_);
lean_dec(v_fst_1062_);
lean_dec(v_a_983_);
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
v_a_1083_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1079_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1079_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1070_);
lean_dec_ref(v_arg_1067_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
v___y_985_ = v_fst_1062_;
v___y_986_ = v_fst_1063_;
v___y_987_ = v___x_1075_;
v___y_988_ = v_snd_1064_;
v___y_989_ = v___x_1076_;
goto v___jp_984_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec(v_declName_848_);
lean_dec_ref(v_arg_844_);
lean_dec_ref(v_arg_841_);
lean_dec_ref(v_arg_838_);
lean_dec_ref(v_e_799_);
v_a_1159_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_982_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_982_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
v___jp_849_:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_799_, v___y_852_);
lean_dec_ref(v_e_799_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v_a_863_, v___x_864_);
lean_dec(v_a_863_);
v___x_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_866_, 0, v_declName_848_);
v___x_867_ = lean_box(1);
v___x_868_ = l_Lean_Meta_Grind_addNewRawFact(v___y_850_, v___y_851_, v___x_865_, v___x_866_, v___x_867_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v_declName_848_);
v_a_869_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_862_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_862_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
v___jp_877_:
{
if (v___y_880_ == 0)
{
lean_object* v_options_881_; uint8_t v_hasTrace_882_; 
v_options_881_ = lean_ctor_get(v___y_809_, 2);
v_hasTrace_882_ = lean_ctor_get_uint8(v_options_881_, sizeof(void*)*1);
if (v_hasTrace_882_ == 0)
{
v___y_850_ = v___y_878_;
v___y_851_ = v___y_879_;
v___y_852_ = v___y_801_;
v___y_853_ = v___y_802_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
goto v___jp_849_;
}
else
{
lean_object* v_inheritedTraceOptions_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_inheritedTraceOptions_883_ = lean_ctor_get(v___y_809_, 13);
v___x_884_ = ((lean_object*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__4));
v___x_885_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__7);
v___x_886_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_883_, v_options_881_, v___x_885_);
if (v___x_886_ == 0)
{
v___y_850_ = v___y_878_;
v___y_851_ = v___y_879_;
v___y_852_ = v___y_801_;
v___y_853_ = v___y_802_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
goto v___jp_849_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_inc(v_declName_848_);
v___x_887_ = l_Lean_MessageData_ofName(v_declName_848_);
v___x_888_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__9);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
lean_inc_ref(v___y_879_);
v___x_890_ = l_Lean_MessageData_ofExpr(v___y_879_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v___x_884_, v___x_891_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_dec_ref_known(v___x_892_, 1);
v___y_850_ = v___y_878_;
v___y_851_ = v___y_879_;
v___y_852_ = v___y_801_;
v___y_853_ = v___y_802_;
v___y_854_ = v___y_803_;
v___y_855_ = v___y_804_;
v___y_856_ = v___y_805_;
v___y_857_ = v___y_806_;
v___y_858_ = v___y_807_;
v___y_859_ = v___y_808_;
v___y_860_ = v___y_809_;
v___y_861_ = v___y_810_;
goto v___jp_849_;
}
else
{
lean_dec_ref(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
return v___x_892_;
}
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v___y_879_);
lean_dec_ref(v___y_878_);
v___x_893_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_805_);
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
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
goto v___jp_812_;
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_896_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_897_ = l_Lean_MessageData_ofName(v_declName_848_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_indentExpr(v_e_799_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__13);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_Meta_Sym_reportIssue(v___x_904_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_dec_ref_known(v___x_905_, 1);
goto v___jp_812_;
}
else
{
return v___x_905_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_906_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_893_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_893_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
v___jp_914_:
{
uint8_t v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
v___x_918_ = 0;
v___x_919_ = 1;
v___x_920_ = l_Lean_Meta_mkLambdaFVars(v_a_917_, v___y_915_, v___x_918_, v___y_916_, v___x_918_, v___y_916_, v___x_919_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v_a_917_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_924_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__3___redArg(v_a_921_, v___y_808_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc_n(v_a_923_, 2);
lean_dec_ref(v___x_922_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
v___x_924_ = lean_infer_type(v_a_923_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; uint8_t v___x_926_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = l_Lean_Expr_hasMVar(v_a_923_);
if (v___x_926_ == 0)
{
uint8_t v___x_927_; 
v___x_927_ = l_Lean_Expr_hasMVar(v_a_925_);
v___y_878_ = v_a_923_;
v___y_879_ = v_a_925_;
v___y_880_ = v___x_927_;
goto v___jp_877_;
}
else
{
v___y_878_ = v_a_923_;
v___y_879_ = v_a_925_;
v___y_880_ = v___y_916_;
goto v___jp_877_;
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_a_923_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_928_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_924_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_936_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_920_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_920_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
v___jp_944_:
{
if (lean_obj_tag(v___y_947_) == 0)
{
lean_object* v_a_948_; 
v_a_948_ = lean_ctor_get(v___y_947_, 0);
lean_inc(v_a_948_);
lean_dec_ref_known(v___y_947_, 1);
v___y_915_ = v___y_945_;
v___y_916_ = v___y_946_;
v_a_917_ = v_a_948_;
goto v___jp_914_;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v___y_945_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_949_ = lean_ctor_get(v___y_947_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___y_947_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___y_947_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___y_947_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
v___jp_957_:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_805_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; uint8_t v_verbose_961_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v_verbose_961_ = lean_ctor_get_uint8(v_a_960_, 0);
lean_dec(v_a_960_);
if (v_verbose_961_ == 0)
{
lean_dec_ref(v___y_958_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
goto v___jp_815_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_962_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__11);
v___x_963_ = l_Lean_MessageData_ofName(v_declName_848_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__2___closed__4);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_indentExpr(v_e_799_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15, &l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15_once, _init_l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___closed__15);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_indentExpr(v___y_958_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = l_Lean_Meta_Sym_reportIssue(v___x_972_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_dec_ref_known(v___x_973_, 1);
goto v___jp_815_;
}
else
{
return v___x_973_;
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___y_958_);
lean_dec(v_declName_848_);
lean_dec_ref(v_e_799_);
v_a_974_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_959_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_959_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
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
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_a_825_);
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
v_a_1168_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_826_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_826_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_thm_800_);
lean_dec_ref(v_e_799_);
v_a_1176_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_824_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_824_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
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
v___jp_821_:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed(lean_object* v_e_1184_, lean_object* v_thm_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_Grind_instantiateExtTheorem___lam__1(v_e_1184_, v_thm_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem(lean_object* v_thm_1198_, lean_object* v_e_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___f_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; 
v___f_1211_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instantiateExtTheorem___lam__1___boxed), 13, 2);
lean_closure_set(v___f_1211_, 0, v_e_1199_);
lean_closure_set(v___f_1211_, 1, v_thm_1198_);
v___x_1212_ = 0;
v___x_1213_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__6___redArg(v___f_1211_, v___x_1212_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instantiateExtTheorem___boxed(lean_object* v_thm_1214_, lean_object* v_e_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Meta_Grind_instantiateExtTheorem(v_thm_1214_, v_e_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(lean_object* v_mvarId_1228_, lean_object* v_val_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___redArg(v_mvarId_1228_, v_val_1229_, v___y_1237_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0___boxed(lean_object* v_mvarId_1242_, lean_object* v_val_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0(v_mvarId_1242_, v_val_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec(v___y_1244_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(lean_object* v_mvarId_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___redArg(v_mvarId_1256_, v___y_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1___boxed(lean_object* v_mvarId_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1(v_mvarId_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec(v_mvarId_1269_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(lean_object* v_cls_1282_, lean_object* v_msg_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___redArg(v_cls_1282_, v_msg_1283_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4___boxed(lean_object* v_cls_1296_, lean_object* v_msg_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_addTrace___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__4(v_cls_1296_, v_msg_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0___redArg(v_x_1311_, v_x_1312_, v_x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(lean_object* v_00_u03b2_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___redArg(v_x_1316_, v_x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1319_, lean_object* v_x_1320_, lean_object* v_x_1321_){
_start:
{
uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_res_1322_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2(v_00_u03b2_1319_, v_x_1320_, v_x_1321_);
lean_dec(v_x_1321_);
lean_dec_ref(v_x_1320_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, size_t v_x_1326_, size_t v_x_1327_, lean_object* v_x_1328_, lean_object* v_x_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___redArg(v_x_1325_, v_x_1326_, v_x_1327_, v_x_1328_, v_x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
size_t v_x_216501__boxed_1337_; size_t v_x_216502__boxed_1338_; lean_object* v_res_1339_; 
v_x_216501__boxed_1337_ = lean_unbox_usize(v_x_1333_);
lean_dec(v_x_1333_);
v_x_216502__boxed_1338_ = lean_unbox_usize(v_x_1334_);
lean_dec(v_x_1334_);
v_res_1339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3(v_00_u03b2_1331_, v_x_1332_, v_x_216501__boxed_1337_, v_x_216502__boxed_1338_, v_x_1335_, v_x_1336_);
return v_res_1339_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_1340_, lean_object* v_x_1341_, size_t v_x_1342_, lean_object* v_x_1343_){
_start:
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___redArg(v_x_1341_, v_x_1342_, v_x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
size_t v_x_216518__boxed_1349_; uint8_t v_res_1350_; lean_object* v_r_1351_; 
v_x_216518__boxed_1349_ = lean_unbox_usize(v_x_1347_);
lean_dec(v_x_1347_);
v_res_1350_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6(v_00_u03b2_1345_, v_x_1346_, v_x_216518__boxed_1349_, v_x_1348_);
lean_dec(v_x_1348_);
lean_dec_ref(v_x_1346_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9(lean_object* v_00_u03b2_1352_, lean_object* v_n_1353_, lean_object* v_k_1354_, lean_object* v_v_1355_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9___redArg(v_n_1353_, v_k_1354_, v_v_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(lean_object* v_00_u03b2_1357_, size_t v_depth_1358_, lean_object* v_keys_1359_, lean_object* v_vals_1360_, lean_object* v_heq_1361_, lean_object* v_i_1362_, lean_object* v_entries_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___redArg(v_depth_1358_, v_keys_1359_, v_vals_1360_, v_i_1362_, v_entries_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10___boxed(lean_object* v_00_u03b2_1365_, lean_object* v_depth_1366_, lean_object* v_keys_1367_, lean_object* v_vals_1368_, lean_object* v_heq_1369_, lean_object* v_i_1370_, lean_object* v_entries_1371_){
_start:
{
size_t v_depth_boxed_1372_; lean_object* v_res_1373_; 
v_depth_boxed_1372_ = lean_unbox_usize(v_depth_1366_);
lean_dec(v_depth_1366_);
v_res_1373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__10(v_00_u03b2_1365_, v_depth_boxed_1372_, v_keys_1367_, v_vals_1368_, v_heq_1369_, v_i_1370_, v_entries_1371_);
lean_dec_ref(v_vals_1368_);
lean_dec_ref(v_keys_1367_);
return v_res_1373_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(lean_object* v_00_u03b2_1374_, lean_object* v_keys_1375_, lean_object* v_vals_1376_, lean_object* v_heq_1377_, lean_object* v_i_1378_, lean_object* v_k_1379_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___redArg(v_keys_1375_, v_i_1378_, v_k_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13___boxed(lean_object* v_00_u03b2_1381_, lean_object* v_keys_1382_, lean_object* v_vals_1383_, lean_object* v_heq_1384_, lean_object* v_i_1385_, lean_object* v_k_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__1_spec__2_spec__6_spec__13(v_00_u03b2_1381_, v_keys_1382_, v_vals_1383_, v_heq_1384_, v_i_1385_, v_k_1386_);
lean_dec(v_k_1386_);
lean_dec_ref(v_vals_1383_);
lean_dec_ref(v_keys_1382_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11(lean_object* v_00_u03b2_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_instantiateExtTheorem_spec__0_spec__0_spec__3_spec__9_spec__11___redArg(v_x_1390_, v_x_1391_, v_x_1392_, v_x_1393_);
return v___x_1394_;
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
