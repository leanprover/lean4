// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Simproc
// Imports: public import Lean.Compiler.InitAttr public import Lean.Meta.Tactic.Simp.Types
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TransformStep_toStep(lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_initializing();
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1481072680____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1481072680____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSimprocDeclsRef;
static const lean_array_object l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl_default = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl = (const lean_object*)&l_Lean_Meta_Simp_instInhabitedSimprocDecl_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocDecl_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDecl_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_SimprocDecl_lt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Simp_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_initFn___lam__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_initFn___lam__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simprocDeclExt"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 22, 242, 0, 82, 247, 8, 246)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocDeclExt;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "Invalid builtin simproc declaration: It can only be registered during initialization"};
static const lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1;
static const lean_string_object l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid builtin simproc declaration `"};
static const lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "`: This builtin simproc has already been declared"};
static const lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_registerSimproc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_registerSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_registerSimproc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__2;
static const lean_string_object l_Lean_Meta_Simp_registerSimproc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Invalid simproc declaration `"};
static const lean_object* l_Lean_Meta_Simp_registerSimproc___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_registerSimproc___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Simp_registerSimproc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__4;
static const lean_string_object l_Lean_Meta_Simp_registerSimproc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "`: This simproc has already been declared"};
static const lean_object* l_Lean_Meta_Simp_registerSimproc___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_registerSimproc___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_registerSimproc___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__6;
static const lean_string_object l_Lean_Meta_Simp_registerSimproc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "`: This function is declared in an imported module"};
static const lean_object* l_Lean_Meta_Simp_registerSimproc___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_registerSimproc___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_registerSimproc___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_registerSimproc___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_instBEqSimprocEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instBEqSimprocEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry = (const lean_object*)&l_Lean_Meta_Simp_instBEqSimprocEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_instToFormatSimprocEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_instToFormatSimprocEntry___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_instToFormatSimprocEntry___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry = (const lean_object*)&l_Lean_Meta_Simp_instToFormatSimprocEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSimprocsRef;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1207380286____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1207380286____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSEvalprocsRef;
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Simproc `"};
static const lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "` has an unexpected type: Expected `Simproc` or `DSimproc`, but found `"};
static const lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DSimproc"};
static const lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_eraseSimprocAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___closed__0;
static const lean_string_object l_Lean_Meta_Simp_eraseSimprocAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` does not have a [simproc] attribute"};
static const lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_eraseSimprocAttr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_eraseSimprocAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_addSimprocAttrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Invalid `[simproc]` attribute: `"};
static const lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_addSimprocAttrCore___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttrCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__1;
static const lean_string_object l_Lean_Meta_Simp_addSimprocAttrCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` is not a simproc"};
static const lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_addSimprocAttrCore___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttrCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__5(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Invalid `[builtin_simproc]` attribute: `"};
static const lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not a builtin simproc"};
static const lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Simp_SimprocEntry_try___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_SimprocEntry_try___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_SimprocEntry_try___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(66, 96, 215, 110, 82, 218, 253, 207)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "simproc result "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_simprocCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_simprocCore___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_simprocCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_simprocCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "no "};
static const lean_object* l_Lean_Meta_Simp_simprocCore___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_simprocCore___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_simprocCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__2;
static const lean_string_object l_Lean_Meta_Simp_simprocCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "-simprocs found for "};
static const lean_object* l_Lean_Meta_Simp_simprocCore___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_simprocCore___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Simp_simprocCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_simprocCore___closed__4;
static const lean_ctor_object l_Lean_Meta_Simp_simprocCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_simprocCore___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_simprocCore___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp_simprocCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l_Lean_Meta_Simp_simprocCore___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_simprocCore___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_simprocCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "post"};
static const lean_object* l_Lean_Meta_Simp_simprocCore___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_simprocCore___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_dsimprocCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_dsimprocCore___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_dsimprocCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_simprocArrayCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_simprocArrayCore___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_simprocArrayCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simprocs"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(126, 212, 8, 196, 39, 220, 153, 228)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "Enable/disable `simproc`s (simplification procedures)."};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(231, 142, 91, 215, 4, 141, 43, 74)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocs;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2_value;
static const lean_array_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__12_value;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25;
static lean_once_cell_t l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___auto__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__5___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_mkSimprocExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkSimprocExt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___closed__0_value;
static const lean_closure_object l_Lean_Meta_Simp_mkSimprocExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkSimprocExt___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___closed__1_value;
static const lean_closure_object l_Lean_Meta_Simp_mkSimprocExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___closed__2_value;
static const lean_closure_object l_Lean_Meta_Simp_mkSimprocExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___closed__3_value;
static const lean_closure_object l_Lean_Meta_Simp_mkSimprocExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_mkSimprocExt___lam__5___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_mkSimprocExt___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_addSimprocAttr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__4;
static const lean_string_object l_Lean_Meta_Simp_addSimprocAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_addSimprocAttr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_addSimprocAttr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_addSimprocAttr___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_addSimprocAttr___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Simp_addSimprocAttr___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_addSimprocAttr___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Simp_addSimprocAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_addSimprocAttr___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_addSimprocAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Simp_addSimprocAttr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_addSimprocAttr___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocExtensionMapRef;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr___auto__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simprocAttr"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 224, 78, 200, 71, 50, 151, 250)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Simplification procedure"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simprocExtension"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 72, 162, 209, 248, 181, 187, 248)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocExtension;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "sevalprocAttr"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 205, 179, 175, 177, 80, 141, 171)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Symbolic evaluator procedure"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "simprocSEvalExtension"};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 203, 14, 198, 243, 211, 154, 228)}};
static const lean_object* l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocSEvalExtension;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Unexpected simproc type: Expected "};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(18, 160, 179, 254, 130, 82, 156, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " or "};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(119, 227, 62, 233, 71, 149, 243, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ", but `"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13_value),LEAN_SCALAR_PTR_LITERAL(187, 118, 236, 113, 107, 136, 194, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__21_value),LEAN_SCALAR_PTR_LITERAL(236, 33, 85, 75, 207, 191, 2, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__22_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__23;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Not implemented yet, [-builtin_simproc]"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "addSimprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 9, 234, 253, 232, 127, 99, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(131, 185, 68, 160, 42, 232, 242, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(206, 162, 193, 135, 58, 124, 36, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 156, 38, 170, 47, 144, 113, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 119, 125, 213, 148, 207, 89, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 80, 126, 51, 77, 164, 99, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 207, 53, 220, 0, 110, 233, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__14_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__15_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 3, 153, 63, 253, 49, 95, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__16_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 18, 209, 36, 122, 47, 172, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__17_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 144, 247, 160, 142, 132, 41, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__18_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 103, 177, 120, 64, 206, 153, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__19_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 13, 210, 143, 245, 58, 61, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__20_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(115, 217, 78, 63, 204, 44, 77, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1616411946) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(209, 17, 207, 102, 181, 6, 180, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__22_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 162, 42, 63, 10, 6, 120, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__24_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 58, 110, 169, 187, 150, 63, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__26_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(111, 218, 218, 24, 22, 31, 109, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "simprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__28_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 156, 85, 144, 105, 22, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Builtin simplification procedure"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__27_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__29_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__30_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__31_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Not implemented yet, [-builtin_sevalproc]"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "addSEvalprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed, .m_arity = 9, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__21_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1544969214) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(149, 170, 72, 228, 230, 78, 20, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__23_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 12, 2, 172, 64, 98, 147, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__25_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 71, 61, 72, 148, 76, 126, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(35, 31, 172, 49, 129, 10, 175, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sevalprocBuiltinAttr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 143, 67, 175, 129, 184, 58, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Builtin symbolic evaluation procedure"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__8_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 61, 75, 186, 44, 210, 52, 194)}};
static const lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "seval"};
static const lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(203, 151, 253, 192, 151, 99, 156, 151)}};
static const lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_proc"};
static const lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__0, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default;
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1481072680____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__2);
v___x_13_ = lean_st_mk_ref(v___x_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1481072680____hygCtx___hyg_2____boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1481072680____hygCtx___hyg_2_();
return v_res_16_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__0(void){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__0, &l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__0_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__0);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__2(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1);
v___x_28_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__2, &l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__2_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__2);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default;
return v___x_31_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocDecl_lt(lean_object* v_decl_u2081_32_, lean_object* v_decl_u2082_33_){
_start:
{
lean_object* v_declName_34_; lean_object* v_declName_35_; uint8_t v___x_36_; 
v_declName_34_ = lean_ctor_get(v_decl_u2081_32_, 0);
v_declName_35_ = lean_ctor_get(v_decl_u2082_33_, 0);
v___x_36_ = l_Lean_Name_quickLt(v_declName_34_, v_declName_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDecl_lt___boxed(lean_object* v_decl_u2081_37_, lean_object* v_decl_u2082_38_){
_start:
{
uint8_t v_res_39_; lean_object* v_r_40_; 
v_res_39_ = l_Lean_Meta_Simp_SimprocDecl_lt(v_decl_u2081_37_, v_decl_u2082_38_);
lean_dec_ref(v_decl_u2082_38_);
lean_dec_ref(v_decl_u2081_37_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_41_, lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
lean_object* v_ks_45_; lean_object* v_vs_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_70_; 
v_ks_45_ = lean_ctor_get(v_x_41_, 0);
v_vs_46_ = lean_ctor_get(v_x_41_, 1);
v_isSharedCheck_70_ = !lean_is_exclusive(v_x_41_);
if (v_isSharedCheck_70_ == 0)
{
v___x_48_ = v_x_41_;
v_isShared_49_ = v_isSharedCheck_70_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_vs_46_);
lean_inc(v_ks_45_);
lean_dec(v_x_41_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_70_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_array_get_size(v_ks_45_);
v___x_51_ = lean_nat_dec_lt(v_x_42_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
lean_dec(v_x_42_);
v___x_52_ = lean_array_push(v_ks_45_, v_x_43_);
v___x_53_ = lean_array_push(v_vs_46_, v_x_44_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v___x_53_);
lean_ctor_set(v___x_48_, 0, v___x_52_);
v___x_55_ = v___x_48_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
else
{
lean_object* v_k_x27_57_; uint8_t v___x_58_; 
v_k_x27_57_ = lean_array_fget_borrowed(v_ks_45_, v_x_42_);
v___x_58_ = lean_name_eq(v_x_43_, v_k_x27_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_60_; 
if (v_isShared_49_ == 0)
{
v___x_60_ = v___x_48_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_ks_45_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_vs_46_);
v___x_60_ = v_reuseFailAlloc_64_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_x_42_, v___x_61_);
lean_dec(v_x_42_);
v_x_41_ = v___x_60_;
v_x_42_ = v___x_62_;
goto _start;
}
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_65_ = lean_array_fset(v_ks_45_, v_x_42_, v_x_43_);
v___x_66_ = lean_array_fset(v_vs_46_, v_x_42_, v_x_44_);
lean_dec(v_x_42_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v___x_66_);
lean_ctor_set(v___x_48_, 0, v___x_65_);
v___x_68_ = v___x_48_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_n_71_, lean_object* v_k_72_, lean_object* v_v_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(0u);
v___x_75_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_n_71_, v___x_74_, v_k_72_, v_v_73_);
return v___x_75_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_76_; uint64_t v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(1723u);
v___x_77_ = lean_uint64_of_nat(v___x_76_);
return v___x_77_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_78_; size_t v___x_79_; size_t v___x_80_; 
v___x_78_ = ((size_t)5ULL);
v___x_79_ = ((size_t)1ULL);
v___x_80_ = lean_usize_shift_left(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; 
v___x_81_ = ((size_t)1ULL);
v___x_82_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_83_ = lean_usize_sub(v___x_82_, v___x_81_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_85_, size_t v_x_86_, size_t v_x_87_, lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_es_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v_j_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_es_90_ = lean_ctor_get(v_x_85_, 0);
v___x_91_ = ((size_t)5ULL);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_94_ = lean_usize_land(v_x_86_, v___x_93_);
v_j_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_array_get_size(v_es_90_);
v___x_97_ = lean_nat_dec_lt(v_j_95_, v___x_96_);
if (v___x_97_ == 0)
{
lean_dec(v_j_95_);
lean_dec(v_x_89_);
lean_dec(v_x_88_);
return v_x_85_;
}
else
{
lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_134_; 
lean_inc_ref(v_es_90_);
v_isSharedCheck_134_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_134_ == 0)
{
lean_object* v_unused_135_; 
v_unused_135_ = lean_ctor_get(v_x_85_, 0);
lean_dec(v_unused_135_);
v___x_99_ = v_x_85_;
v_isShared_100_ = v_isSharedCheck_134_;
goto v_resetjp_98_;
}
else
{
lean_dec(v_x_85_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_134_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_v_101_; lean_object* v___x_102_; lean_object* v_xs_x27_103_; lean_object* v___y_105_; 
v_v_101_ = lean_array_fget(v_es_90_, v_j_95_);
v___x_102_ = lean_box(0);
v_xs_x27_103_ = lean_array_fset(v_es_90_, v_j_95_, v___x_102_);
switch(lean_obj_tag(v_v_101_))
{
case 0:
{
lean_object* v_key_110_; lean_object* v_val_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_121_; 
v_key_110_ = lean_ctor_get(v_v_101_, 0);
v_val_111_ = lean_ctor_get(v_v_101_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_121_ == 0)
{
v___x_113_ = v_v_101_;
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_val_111_);
lean_inc(v_key_110_);
lean_dec(v_v_101_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_121_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
uint8_t v___x_115_; 
v___x_115_ = lean_name_eq(v_x_88_, v_key_110_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_del_object(v___x_113_);
v___x_116_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_110_, v_val_111_, v_x_88_, v_x_89_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
lean_dec(v_val_111_);
lean_dec(v_key_110_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v_x_89_);
lean_ctor_set(v___x_113_, 0, v_x_88_);
v___x_119_ = v___x_113_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_x_88_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_x_89_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
}
}
}
case 1:
{
lean_object* v_node_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_node_122_ = lean_ctor_get(v_v_101_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_132_ == 0)
{
v___x_124_ = v_v_101_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_node_122_);
lean_dec(v_v_101_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_126_ = lean_usize_shift_right(v_x_86_, v___x_91_);
v___x_127_ = lean_usize_add(v_x_87_, v___x_92_);
v___x_128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_node_122_, v___x_126_, v___x_127_, v_x_88_, v_x_89_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_128_);
v___x_130_ = v___x_124_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
v___y_105_ = v___x_130_;
goto v___jp_104_;
}
}
}
default: 
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_x_88_);
lean_ctor_set(v___x_133_, 1, v_x_89_);
v___y_105_ = v___x_133_;
goto v___jp_104_;
}
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_106_ = lean_array_fset(v_xs_x27_103_, v_j_95_, v___y_105_);
lean_dec(v_j_95_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_106_);
v___x_108_ = v___x_99_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
lean_object* v_ks_136_; lean_object* v_vs_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_157_; 
v_ks_136_ = lean_ctor_get(v_x_85_, 0);
v_vs_137_ = lean_ctor_get(v_x_85_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_85_);
if (v_isSharedCheck_157_ == 0)
{
v___x_139_ = v_x_85_;
v_isShared_140_ = v_isSharedCheck_157_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_vs_137_);
lean_inc(v_ks_136_);
lean_dec(v_x_85_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_157_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_ks_136_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_vs_137_);
v___x_142_ = v_reuseFailAlloc_156_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v_newNode_143_; uint8_t v___y_145_; size_t v___x_151_; uint8_t v___x_152_; 
v_newNode_143_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_142_, v_x_88_, v_x_89_);
v___x_151_ = ((size_t)7ULL);
v___x_152_ = lean_usize_dec_le(v___x_151_, v_x_87_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_143_);
v___x_154_ = lean_unsigned_to_nat(4u);
v___x_155_ = lean_nat_dec_lt(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
v___y_145_ = v___x_155_;
goto v___jp_144_;
}
else
{
v___y_145_ = v___x_152_;
goto v___jp_144_;
}
v___jp_144_:
{
if (v___y_145_ == 0)
{
lean_object* v_ks_146_; lean_object* v_vs_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_ks_146_ = lean_ctor_get(v_newNode_143_, 0);
lean_inc_ref(v_ks_146_);
v_vs_147_ = lean_ctor_get(v_newNode_143_, 1);
lean_inc_ref(v_vs_147_);
lean_dec_ref(v_newNode_143_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2);
v___x_150_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_87_, v_ks_146_, v_vs_147_, v___x_148_, v___x_149_);
lean_dec_ref(v_vs_147_);
lean_dec_ref(v_ks_146_);
return v___x_150_;
}
else
{
return v_newNode_143_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(size_t v_depth_158_, lean_object* v_keys_159_, lean_object* v_vals_160_, lean_object* v_i_161_, lean_object* v_entries_162_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_array_get_size(v_keys_159_);
v___x_164_ = lean_nat_dec_lt(v_i_161_, v___x_163_);
if (v___x_164_ == 0)
{
lean_dec(v_i_161_);
return v_entries_162_;
}
else
{
lean_object* v_k_165_; lean_object* v_v_166_; uint64_t v___y_168_; 
v_k_165_ = lean_array_fget_borrowed(v_keys_159_, v_i_161_);
v_v_166_ = lean_array_fget_borrowed(v_vals_160_, v_i_161_);
if (lean_obj_tag(v_k_165_) == 0)
{
uint64_t v___x_179_; 
v___x_179_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_168_ = v___x_179_;
goto v___jp_167_;
}
else
{
uint64_t v_hash_180_; 
v_hash_180_ = lean_ctor_get_uint64(v_k_165_, sizeof(void*)*2);
v___y_168_ = v_hash_180_;
goto v___jp_167_;
}
v___jp_167_:
{
size_t v_h_169_; size_t v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v_h_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_h_169_ = lean_uint64_to_usize(v___y_168_);
v___x_170_ = ((size_t)5ULL);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_sub(v_depth_158_, v___x_172_);
v___x_174_ = lean_usize_mul(v___x_170_, v___x_173_);
v_h_175_ = lean_usize_shift_right(v_h_169_, v___x_174_);
v___x_176_ = lean_nat_add(v_i_161_, v___x_171_);
lean_dec(v_i_161_);
lean_inc(v_v_166_);
lean_inc(v_k_165_);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_entries_162_, v_h_175_, v_depth_158_, v_k_165_, v_v_166_);
v_i_161_ = v___x_176_;
v_entries_162_ = v___x_177_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_181_, lean_object* v_keys_182_, lean_object* v_vals_183_, lean_object* v_i_184_, lean_object* v_entries_185_){
_start:
{
size_t v_depth_boxed_186_; lean_object* v_res_187_; 
v_depth_boxed_186_ = lean_unbox_usize(v_depth_181_);
lean_dec(v_depth_181_);
v_res_187_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_depth_boxed_186_, v_keys_182_, v_vals_183_, v_i_184_, v_entries_185_);
lean_dec_ref(v_vals_183_);
lean_dec_ref(v_keys_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
size_t v_x_1470__boxed_193_; size_t v_x_1471__boxed_194_; lean_object* v_res_195_; 
v_x_1470__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_x_1471__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_188_, v_x_1470__boxed_193_, v_x_1471__boxed_194_, v_x_191_, v_x_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint64_t v___y_200_; 
if (lean_obj_tag(v_x_197_) == 0)
{
uint64_t v___x_204_; 
v___x_204_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_200_ = v___x_204_;
goto v___jp_199_;
}
else
{
uint64_t v_hash_205_; 
v_hash_205_ = lean_ctor_get_uint64(v_x_197_, sizeof(void*)*2);
v___y_200_ = v_hash_205_;
goto v___jp_199_;
}
v___jp_199_:
{
size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v___x_201_ = lean_uint64_to_usize(v___y_200_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_196_, v___x_201_, v___x_202_, v_x_197_, v_x_198_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v_s_206_, lean_object* v_d_207_){
_start:
{
lean_object* v_builtin_208_; lean_object* v_newEntries_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_219_; 
v_builtin_208_ = lean_ctor_get(v_s_206_, 0);
v_newEntries_209_ = lean_ctor_get(v_s_206_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_s_206_);
if (v_isSharedCheck_219_ == 0)
{
v___x_211_ = v_s_206_;
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_newEntries_209_);
lean_inc(v_builtin_208_);
lean_dec(v_s_206_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_declName_213_; lean_object* v_keys_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v_declName_213_ = lean_ctor_get(v_d_207_, 0);
lean_inc(v_declName_213_);
v_keys_214_ = lean_ctor_get(v_d_207_, 1);
lean_inc_ref(v_keys_214_);
lean_dec_ref(v_d_207_);
v___x_215_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(v_newEntries_209_, v_declName_213_, v_keys_214_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 1, v___x_215_);
v___x_217_ = v___x_211_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_builtin_208_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v_result_220_, lean_object* v_declName_221_, lean_object* v_keys_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_223_, 0, v_declName_221_);
lean_ctor_set(v___x_223_, 1, v_keys_222_);
v___x_224_ = lean_array_push(v_result_220_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(lean_object* v_as_226_, lean_object* v_lo_227_, lean_object* v_hi_228_){
_start:
{
uint8_t v___x_229_; 
v___x_229_ = lean_nat_dec_lt(v_lo_227_, v_hi_228_);
if (v___x_229_ == 0)
{
lean_dec(v_lo_227_);
return v_as_226_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_fst_232_; lean_object* v_snd_233_; uint8_t v___x_234_; 
v___x_230_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg___closed__0));
lean_inc(v_lo_227_);
v___x_231_ = l_Array_qpartition___redArg(v_as_226_, v___x_230_, v_lo_227_, v_hi_228_);
v_fst_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_fst_232_);
v_snd_233_ = lean_ctor_get(v___x_231_, 1);
lean_inc(v_snd_233_);
lean_dec_ref(v___x_231_);
v___x_234_ = lean_nat_dec_le(v_hi_228_, v_fst_232_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_snd_233_, v_lo_227_, v_fst_232_);
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_add(v_fst_232_, v___x_236_);
lean_dec(v_fst_232_);
v_as_226_ = v___x_235_;
v_lo_227_ = v___x_237_;
goto _start;
}
else
{
lean_dec(v_fst_232_);
lean_dec(v_lo_227_);
return v_snd_233_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_as_239_, lean_object* v_lo_240_, lean_object* v_hi_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_as_239_, v_lo_240_, v_hi_241_);
lean_dec(v_hi_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg___lam__0(lean_object* v_f_243_, lean_object* v_x1_244_, lean_object* v_x2_245_, lean_object* v_x3_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = lean_apply_3(v_f_243_, v_x1_244_, v_x2_245_, v_x3_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_f_248_, lean_object* v_keys_249_, lean_object* v_vals_250_, lean_object* v_i_251_, lean_object* v_acc_252_){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = lean_array_get_size(v_keys_249_);
v___x_254_ = lean_nat_dec_lt(v_i_251_, v___x_253_);
if (v___x_254_ == 0)
{
lean_dec(v_i_251_);
lean_dec(v_f_248_);
return v_acc_252_;
}
else
{
lean_object* v_k_255_; lean_object* v_v_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_k_255_ = lean_array_fget_borrowed(v_keys_249_, v_i_251_);
v_v_256_ = lean_array_fget_borrowed(v_vals_250_, v_i_251_);
lean_inc(v_f_248_);
lean_inc(v_v_256_);
lean_inc(v_k_255_);
v___x_257_ = lean_apply_3(v_f_248_, v_acc_252_, v_k_255_, v_v_256_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_i_251_, v___x_258_);
lean_dec(v_i_251_);
v_i_251_ = v___x_259_;
v_acc_252_ = v___x_257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_f_261_, lean_object* v_keys_262_, lean_object* v_vals_263_, lean_object* v_i_264_, lean_object* v_acc_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg(v_f_261_, v_keys_262_, v_vals_263_, v_i_264_, v_acc_265_);
lean_dec_ref(v_vals_263_);
lean_dec_ref(v_keys_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(lean_object* v_f_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v_es_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_es_270_ = lean_ctor_get(v_x_268_, 0);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_array_get_size(v_es_270_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_f_267_);
return v_x_269_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_le(v___x_272_, v___x_272_);
if (v___x_274_ == 0)
{
if (v___x_273_ == 0)
{
lean_dec(v_f_267_);
return v_x_269_;
}
else
{
size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((size_t)0ULL);
v___x_276_ = lean_usize_of_nat(v___x_272_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_f_267_, v_es_270_, v___x_275_, v___x_276_, v_x_269_);
return v___x_277_;
}
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((size_t)0ULL);
v___x_279_ = lean_usize_of_nat(v___x_272_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_f_267_, v_es_270_, v___x_278_, v___x_279_, v_x_269_);
return v___x_280_;
}
}
}
else
{
lean_object* v_ks_281_; lean_object* v_vs_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_ks_281_ = lean_ctor_get(v_x_268_, 0);
v_vs_282_ = lean_ctor_get(v_x_268_, 1);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg(v_f_267_, v_ks_281_, v_vs_282_, v___x_283_, v_x_269_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_f_285_, lean_object* v_as_286_, size_t v_i_287_, size_t v_stop_288_, lean_object* v_b_289_){
_start:
{
lean_object* v___y_291_; uint8_t v___x_295_; 
v___x_295_ = lean_usize_dec_eq(v_i_287_, v_stop_288_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_array_uget_borrowed(v_as_286_, v_i_287_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_key_297_; lean_object* v_val_298_; lean_object* v___x_299_; 
v_key_297_ = lean_ctor_get(v___x_296_, 0);
v_val_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_f_285_);
lean_inc(v_val_298_);
lean_inc(v_key_297_);
v___x_299_ = lean_apply_3(v_f_285_, v_b_289_, v_key_297_, v_val_298_);
v___y_291_ = v___x_299_;
goto v___jp_290_;
}
case 1:
{
lean_object* v_node_300_; lean_object* v___x_301_; 
v_node_300_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_f_285_);
v___x_301_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_f_285_, v_node_300_, v_b_289_);
v___y_291_ = v___x_301_;
goto v___jp_290_;
}
default: 
{
v___y_291_ = v_b_289_;
goto v___jp_290_;
}
}
}
else
{
lean_dec(v_f_285_);
return v_b_289_;
}
v___jp_290_:
{
size_t v___x_292_; size_t v___x_293_; 
v___x_292_ = ((size_t)1ULL);
v___x_293_ = lean_usize_add(v_i_287_, v___x_292_);
v_i_287_ = v___x_293_;
v_b_289_ = v___y_291_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_f_302_, lean_object* v_as_303_, lean_object* v_i_304_, lean_object* v_stop_305_, lean_object* v_b_306_){
_start:
{
size_t v_i_boxed_307_; size_t v_stop_boxed_308_; lean_object* v_res_309_; 
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_stop_boxed_308_ = lean_unbox_usize(v_stop_305_);
lean_dec(v_stop_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_f_302_, v_as_303_, v_i_boxed_307_, v_stop_boxed_308_, v_b_306_);
lean_dec_ref(v_as_303_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_f_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_f_310_, v_x_311_, v_x_312_);
lean_dec_ref(v_x_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg(lean_object* v_map_314_, lean_object* v_f_315_, lean_object* v_init_316_){
_start:
{
lean_object* v___f_317_; lean_object* v___x_318_; 
v___f_317_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_317_, 0, v_f_315_);
v___x_318_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v___f_317_, v_map_314_, v_init_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_map_319_, lean_object* v_f_320_, lean_object* v_init_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg(v_map_319_, v_f_320_, v_init_321_);
lean_dec_ref(v_map_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v___f_325_, lean_object* v_s_326_){
_start:
{
lean_object* v_newEntries_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_result_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_newEntries_327_ = lean_ctor_get(v_s_326_, 1);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v_result_330_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg(v_newEntries_327_, v___f_325_, v___x_329_);
v___x_331_ = lean_array_get_size(v_result_330_);
v___x_332_ = lean_nat_dec_eq(v___x_331_, v___x_328_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___y_336_; uint8_t v___x_340_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_sub(v___x_331_, v___x_333_);
v___x_340_ = lean_nat_dec_le(v___x_328_, v___x_334_);
if (v___x_340_ == 0)
{
lean_inc(v___x_334_);
v___y_336_ = v___x_334_;
goto v___jp_335_;
}
else
{
v___y_336_ = v___x_328_;
goto v___jp_335_;
}
v___jp_335_:
{
uint8_t v___x_337_; 
v___x_337_ = lean_nat_dec_le(v___y_336_, v___x_334_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
lean_dec(v___x_334_);
lean_inc(v___y_336_);
v___x_338_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_result_330_, v___y_336_, v___y_336_);
lean_dec(v___y_336_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_result_330_, v___y_336_, v___x_334_);
lean_dec(v___x_334_);
return v___x_339_;
}
}
}
else
{
return v_result_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object* v___f_341_, lean_object* v_s_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Simp_initFn___lam__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(v___f_341_, v_s_342_);
lean_dec_ref(v_s_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object* v_x_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Simp_initFn___lam__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(v_x_346_);
lean_dec_ref(v_x_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v___f_348_, lean_object* v_x_349_, lean_object* v_s_350_, uint8_t v_x_351_){
_start:
{
lean_object* v_newEntries_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_result_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_newEntries_352_ = lean_ctor_get(v_s_350_, 1);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v_result_355_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg(v_newEntries_352_, v___f_348_, v___x_354_);
v___x_356_ = lean_array_get_size(v_result_355_);
v___x_357_ = lean_nat_dec_eq(v___x_356_, v___x_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___y_361_; uint8_t v___x_365_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_sub(v___x_356_, v___x_358_);
v___x_365_ = lean_nat_dec_le(v___x_353_, v___x_359_);
if (v___x_365_ == 0)
{
lean_inc(v___x_359_);
v___y_361_ = v___x_359_;
goto v___jp_360_;
}
else
{
v___y_361_ = v___x_353_;
goto v___jp_360_;
}
v___jp_360_:
{
uint8_t v___x_362_; 
v___x_362_ = lean_nat_dec_le(v___y_361_, v___x_359_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
lean_dec(v___x_359_);
lean_inc(v___y_361_);
v___x_363_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_result_355_, v___y_361_, v___y_361_);
lean_dec(v___y_361_);
return v___x_363_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_result_355_, v___y_361_, v___x_359_);
lean_dec(v___x_359_);
return v___x_364_;
}
}
}
else
{
return v_result_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object* v___f_366_, lean_object* v_x_367_, lean_object* v_s_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_x_1825__boxed_370_; lean_object* v_res_371_; 
v_x_1825__boxed_370_ = lean_unbox(v_x_369_);
v_res_371_ = l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(v___f_366_, v_x_367_, v_s_368_, v_x_1825__boxed_370_);
lean_dec_ref(v_s_368_);
lean_dec_ref(v_x_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v___x_372_){
_start:
{
lean_object* v___x_374_; lean_object* v_keys_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_384_; 
v___x_374_ = lean_st_ref_get(v___x_372_);
v_keys_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v___x_374_, 1);
lean_dec(v_unused_385_);
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_keys_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_384_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_keys_375_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object* v___x_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Simp_initFn___lam__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(v___x_386_);
lean_dec(v___x_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(lean_object* v___x_389_, lean_object* v_x_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v_keys_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_403_; 
v___x_393_ = lean_st_ref_get(v___x_389_);
v_keys_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_393_, 1);
lean_dec(v_unused_404_);
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_403_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_keys_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_403_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1, &l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default___closed__1);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_keys_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object* v___x_405_, lean_object* v_x_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Simp_initFn___lam__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(v___x_405_, v_x_406_, v___y_407_);
lean_dec_ref(v___y_407_);
lean_dec_ref(v_x_406_);
lean_dec(v___x_405_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_426_; lean_object* v___f_427_; 
v___x_426_ = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
v___f_427_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_427_, 0, v___x_426_);
return v___f_427_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_428_; lean_object* v___f_429_; 
v___x_428_ = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
v___f_429_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_429_, 0, v___x_428_);
return v___f_429_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___f_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_430_ = lean_box(0);
v___x_431_ = lean_box(2);
v___f_432_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___f_433_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___f_434_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___f_435_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__11_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_);
v___f_436_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_);
v___x_437_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__9_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_438_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___f_436_);
lean_ctor_set(v___x_438_, 2, v___f_435_);
lean_ctor_set(v___x_438_, 3, v___f_434_);
lean_ctor_set(v___x_438_, 4, v___f_433_);
lean_ctor_set(v___x_438_, 5, v___f_432_);
lean_ctor_set(v___x_438_, 6, v___x_431_);
lean_ctor_set(v___x_438_, 7, v___x_430_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___f_439_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_440_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__12_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___f_439_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__13_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_);
v___x_444_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_();
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(v_x_448_, v_x_449_, v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1(lean_object* v_00_u03c3_452_, lean_object* v_00_u03b2_453_, lean_object* v_map_454_, lean_object* v_f_455_, lean_object* v_init_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___redArg(v_map_454_, v_f_455_, v_init_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03c3_458_, lean_object* v_00_u03b2_459_, lean_object* v_map_460_, lean_object* v_f_461_, lean_object* v_init_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1(v_00_u03c3_458_, v_00_u03b2_459_, v_map_460_, v_f_461_, v_init_462_);
lean_dec_ref(v_map_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2(lean_object* v_n_464_, lean_object* v_as_465_, lean_object* v_lo_466_, lean_object* v_hi_467_, lean_object* v_w_468_, lean_object* v_hlo_469_, lean_object* v_hhi_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___redArg(v_as_465_, v_lo_466_, v_hi_467_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2___boxed(lean_object* v_n_472_, lean_object* v_as_473_, lean_object* v_lo_474_, lean_object* v_hi_475_, lean_object* v_w_476_, lean_object* v_hlo_477_, lean_object* v_hhi_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__2(v_n_472_, v_as_473_, v_lo_474_, v_hi_475_, v_w_476_, v_hlo_477_, v_hhi_478_);
lean_dec(v_hi_475_);
lean_dec(v_n_472_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_480_, lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_481_, v_x_482_, v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
size_t v_x_2042__boxed_493_; size_t v_x_2043__boxed_494_; lean_object* v_res_495_; 
v_x_2042__boxed_493_ = lean_unbox_usize(v_x_489_);
lean_dec(v_x_489_);
v_x_2043__boxed_494_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_res_495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_487_, v_x_488_, v_x_2042__boxed_493_, v_x_2043__boxed_494_, v_x_491_, v_x_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_map_496_, lean_object* v_f_497_, lean_object* v_init_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_f_497_, v_map_496_, v_init_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_map_500_, lean_object* v_f_501_, lean_object* v_init_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_500_, v_f_501_, v_init_502_);
lean_dec_ref(v_map_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03c3_504_, lean_object* v_00_u03b2_505_, lean_object* v_map_506_, lean_object* v_f_507_, lean_object* v_init_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_f_507_, v_map_506_, v_init_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03c3_510_, lean_object* v_00_u03b2_511_, lean_object* v_map_512_, lean_object* v_f_513_, lean_object* v_init_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2(v_00_u03c3_510_, v_00_u03b2_511_, v_map_512_, v_f_513_, v_init_514_);
lean_dec_ref(v_map_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_516_, lean_object* v_n_517_, lean_object* v_k_518_, lean_object* v_v_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_n_517_, v_k_518_, v_v_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_521_, size_t v_depth_522_, lean_object* v_keys_523_, lean_object* v_vals_524_, lean_object* v_heq_525_, lean_object* v_i_526_, lean_object* v_entries_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_depth_522_, v_keys_523_, v_vals_524_, v_i_526_, v_entries_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_529_, lean_object* v_depth_530_, lean_object* v_keys_531_, lean_object* v_vals_532_, lean_object* v_heq_533_, lean_object* v_i_534_, lean_object* v_entries_535_){
_start:
{
size_t v_depth_boxed_536_; lean_object* v_res_537_; 
v_depth_boxed_536_ = lean_unbox_usize(v_depth_530_);
lean_dec(v_depth_530_);
v_res_537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_529_, v_depth_boxed_536_, v_keys_531_, v_vals_532_, v_heq_533_, v_i_534_, v_entries_535_);
lean_dec_ref(v_vals_532_);
lean_dec_ref(v_keys_531_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_00_u03c3_538_, lean_object* v_00_u03b1_539_, lean_object* v_00_u03b2_540_, lean_object* v_f_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_f_541_, v_x_542_, v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03c3_545_, lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_f_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_00_u03c3_545_, v_00_u03b1_546_, v_00_u03b2_547_, v_f_548_, v_x_549_, v_x_550_);
lean_dec_ref(v_x_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_x_553_, v_x_554_, v_x_555_, v_x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_00_u03c3_560_, lean_object* v_f_561_, lean_object* v_as_562_, size_t v_i_563_, size_t v_stop_564_, lean_object* v_b_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_f_561_, v_as_562_, v_i_563_, v_stop_564_, v_b_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_00_u03c3_569_, lean_object* v_f_570_, lean_object* v_as_571_, lean_object* v_i_572_, lean_object* v_stop_573_, lean_object* v_b_574_){
_start:
{
size_t v_i_boxed_575_; size_t v_stop_boxed_576_; lean_object* v_res_577_; 
v_i_boxed_575_ = lean_unbox_usize(v_i_572_);
lean_dec(v_i_572_);
v_stop_boxed_576_ = lean_unbox_usize(v_stop_573_);
lean_dec(v_stop_573_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(v_00_u03b1_567_, v_00_u03b2_568_, v_00_u03c3_569_, v_f_570_, v_as_571_, v_i_boxed_575_, v_stop_boxed_576_, v_b_574_);
lean_dec_ref(v_as_571_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03c3_578_, lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_f_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_heq_584_, lean_object* v_i_585_, lean_object* v_acc_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___redArg(v_f_581_, v_keys_582_, v_vals_583_, v_i_585_, v_acc_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03c3_588_, lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_f_591_, lean_object* v_keys_592_, lean_object* v_vals_593_, lean_object* v_heq_594_, lean_object* v_i_595_, lean_object* v_acc_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__9(v_00_u03c3_588_, v_00_u03b1_589_, v_00_u03b2_590_, v_f_591_, v_keys_592_, v_vals_593_, v_heq_594_, v_i_595_, v_acc_596_);
lean_dec_ref(v_vals_593_);
lean_dec_ref(v_keys_592_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg(lean_object* v_a_598_, lean_object* v_x_599_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
return v___x_600_;
}
else
{
lean_object* v_key_601_; lean_object* v_value_602_; lean_object* v_tail_603_; uint8_t v___x_604_; 
v_key_601_ = lean_ctor_get(v_x_599_, 0);
v_value_602_ = lean_ctor_get(v_x_599_, 1);
v_tail_603_ = lean_ctor_get(v_x_599_, 2);
v___x_604_ = lean_name_eq(v_key_601_, v_a_598_);
if (v___x_604_ == 0)
{
v_x_599_ = v_tail_603_;
goto _start;
}
else
{
lean_object* v___x_606_; 
lean_inc(v_value_602_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_value_602_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_607_, lean_object* v_x_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_a_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(lean_object* v_m_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_buckets_612_; lean_object* v___x_613_; uint64_t v___y_615_; 
v_buckets_612_ = lean_ctor_get(v_m_610_, 1);
v___x_613_ = lean_array_get_size(v_buckets_612_);
if (lean_obj_tag(v_a_611_) == 0)
{
uint64_t v___x_629_; 
v___x_629_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_615_ = v___x_629_;
goto v___jp_614_;
}
else
{
uint64_t v_hash_630_; 
v_hash_630_ = lean_ctor_get_uint64(v_a_611_, sizeof(void*)*2);
v___y_615_ = v_hash_630_;
goto v___jp_614_;
}
v___jp_614_:
{
uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v_fold_618_; uint64_t v___x_619_; uint64_t v___x_620_; uint64_t v___x_621_; size_t v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_616_ = 32ULL;
v___x_617_ = lean_uint64_shift_right(v___y_615_, v___x_616_);
v_fold_618_ = lean_uint64_xor(v___y_615_, v___x_617_);
v___x_619_ = 16ULL;
v___x_620_ = lean_uint64_shift_right(v_fold_618_, v___x_619_);
v___x_621_ = lean_uint64_xor(v_fold_618_, v___x_620_);
v___x_622_ = lean_uint64_to_usize(v___x_621_);
v___x_623_ = lean_usize_of_nat(v___x_613_);
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_sub(v___x_623_, v___x_624_);
v___x_626_ = lean_usize_land(v___x_622_, v___x_625_);
v___x_627_ = lean_array_uget_borrowed(v_buckets_612_, v___x_626_);
v___x_628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_611_, v___x_627_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* v_m_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v_m_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_m_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg(lean_object* v_as_634_, lean_object* v_k_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_m_640_; lean_object* v_a_641_; uint8_t v___x_642_; 
v___x_638_ = lean_nat_add(v_x_636_, v_x_637_);
v___x_639_ = lean_unsigned_to_nat(1u);
v_m_640_ = lean_nat_shiftr(v___x_638_, v___x_639_);
lean_dec(v___x_638_);
v_a_641_ = lean_array_fget_borrowed(v_as_634_, v_m_640_);
v___x_642_ = l_Lean_Meta_Simp_SimprocDecl_lt(v_a_641_, v_k_635_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
lean_dec(v_x_637_);
v___x_643_ = l_Lean_Meta_Simp_SimprocDecl_lt(v_k_635_, v_a_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec(v_m_640_);
lean_dec(v_x_636_);
lean_inc(v_a_641_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v_a_641_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_nat_dec_eq(v_m_640_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_nat_sub(v_m_640_, v___x_639_);
lean_dec(v_m_640_);
v___x_648_ = lean_nat_dec_lt(v___x_647_, v_x_636_);
if (v___x_648_ == 0)
{
v_x_637_ = v___x_647_;
goto _start;
}
else
{
lean_object* v___x_650_; 
lean_dec(v___x_647_);
lean_dec(v_x_636_);
v___x_650_ = lean_box(0);
return v___x_650_;
}
}
else
{
lean_object* v___x_651_; 
lean_dec(v_m_640_);
lean_dec(v_x_636_);
v___x_651_ = lean_box(0);
return v___x_651_;
}
}
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
lean_dec(v_x_636_);
v___x_652_ = lean_nat_add(v_m_640_, v___x_639_);
lean_dec(v_m_640_);
v___x_653_ = lean_nat_dec_le(v___x_652_, v_x_637_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec(v___x_652_);
lean_dec(v_x_637_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
else
{
v_x_636_ = v___x_652_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg___boxed(lean_object* v_as_656_, lean_object* v_k_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg(v_as_656_, v_k_657_, v_x_658_, v_x_659_);
lean_dec_ref(v_k_657_);
lean_dec_ref(v_as_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_661_, lean_object* v_vals_662_, lean_object* v_i_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_array_get_size(v_keys_661_);
v___x_666_ = lean_nat_dec_lt(v_i_663_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec(v_i_663_);
v___x_667_ = lean_box(0);
return v___x_667_;
}
else
{
lean_object* v_k_x27_668_; uint8_t v___x_669_; 
v_k_x27_668_ = lean_array_fget_borrowed(v_keys_661_, v_i_663_);
v___x_669_ = lean_name_eq(v_k_664_, v_k_x27_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_i_663_, v___x_670_);
lean_dec(v_i_663_);
v_i_663_ = v___x_671_;
goto _start;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_array_fget_borrowed(v_vals_662_, v_i_663_);
lean_dec(v_i_663_);
lean_inc(v___x_673_);
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_675_, lean_object* v_vals_676_, lean_object* v_i_677_, lean_object* v_k_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_675_, v_vals_676_, v_i_677_, v_k_678_);
lean_dec(v_k_678_);
lean_dec_ref(v_vals_676_);
lean_dec_ref(v_keys_675_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg(lean_object* v_x_680_, size_t v_x_681_, lean_object* v_x_682_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_object* v_es_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_704_; 
v_es_683_ = lean_ctor_get(v_x_680_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_704_ == 0)
{
v___x_685_ = v_x_680_;
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_es_683_);
lean_dec(v_x_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; size_t v___x_688_; size_t v___x_689_; size_t v___x_690_; lean_object* v_j_691_; lean_object* v___x_692_; 
v___x_687_ = lean_box(2);
v___x_688_ = ((size_t)5ULL);
v___x_689_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_690_ = lean_usize_land(v_x_681_, v___x_689_);
v_j_691_ = lean_usize_to_nat(v___x_690_);
v___x_692_ = lean_array_get(v___x_687_, v_es_683_, v_j_691_);
lean_dec(v_j_691_);
lean_dec_ref(v_es_683_);
switch(lean_obj_tag(v___x_692_))
{
case 0:
{
lean_object* v_key_693_; lean_object* v_val_694_; uint8_t v___x_695_; 
v_key_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_key_693_);
v_val_694_ = lean_ctor_get(v___x_692_, 1);
lean_inc(v_val_694_);
lean_dec_ref(v___x_692_);
v___x_695_ = lean_name_eq(v_x_682_, v_key_693_);
lean_dec(v_key_693_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v_val_694_);
lean_del_object(v___x_685_);
v___x_696_ = lean_box(0);
return v___x_696_;
}
else
{
lean_object* v___x_698_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 1);
lean_ctor_set(v___x_685_, 0, v_val_694_);
v___x_698_ = v___x_685_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_val_694_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
case 1:
{
lean_object* v_node_700_; size_t v___x_701_; 
lean_del_object(v___x_685_);
v_node_700_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_node_700_);
lean_dec_ref(v___x_692_);
v___x_701_ = lean_usize_shift_right(v_x_681_, v___x_688_);
v_x_680_ = v_node_700_;
v_x_681_ = v___x_701_;
goto _start;
}
default: 
{
lean_object* v___x_703_; 
lean_del_object(v___x_685_);
v___x_703_ = lean_box(0);
return v___x_703_;
}
}
}
}
else
{
lean_object* v_ks_705_; lean_object* v_vs_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_ks_705_ = lean_ctor_get(v_x_680_, 0);
lean_inc_ref(v_ks_705_);
v_vs_706_ = lean_ctor_get(v_x_680_, 1);
lean_inc_ref(v_vs_706_);
lean_dec_ref(v_x_680_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_705_, v_vs_706_, v___x_707_, v_x_682_);
lean_dec_ref(v_vs_706_);
lean_dec_ref(v_ks_705_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
size_t v_x_1442__boxed_712_; lean_object* v_res_713_; 
v_x_1442__boxed_712_ = lean_unbox_usize(v_x_710_);
lean_dec(v_x_710_);
v_res_713_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_709_, v_x_1442__boxed_712_, v_x_711_);
lean_dec(v_x_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
uint64_t v___y_717_; 
if (lean_obj_tag(v_x_715_) == 0)
{
uint64_t v___x_720_; 
v___x_720_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_717_ = v___x_720_;
goto v___jp_716_;
}
else
{
uint64_t v_hash_721_; 
v_hash_721_ = lean_ctor_get_uint64(v_x_715_, sizeof(void*)*2);
v___y_717_ = v_hash_721_;
goto v___jp_716_;
}
v___jp_716_:
{
size_t v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_uint64_to_usize(v___y_717_);
v___x_719_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_714_, v___x_718_, v_x_715_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg___boxed(lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg(v_x_722_, v_x_723_);
lean_dec(v_x_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(lean_object* v_declName_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_730_; lean_object* v_env_731_; lean_object* v___x_732_; lean_object* v___x_742_; 
v___x_730_ = lean_st_ref_get(v_a_728_);
v_env_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc_ref(v_env_731_);
lean_dec(v___x_730_);
v___x_732_ = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default;
v___x_742_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_731_, v_declName_727_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; lean_object* v_toEnvExtension_744_; lean_object* v_asyncMode_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v_newEntries_748_; lean_object* v___x_749_; 
v___x_743_ = l_Lean_Meta_Simp_simprocDeclExt;
v_toEnvExtension_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_toEnvExtension_744_);
v_asyncMode_745_ = lean_ctor_get(v_toEnvExtension_744_, 2);
lean_inc(v_asyncMode_745_);
lean_dec_ref(v_toEnvExtension_744_);
v___x_746_ = lean_box(0);
lean_inc_ref(v_env_731_);
v___x_747_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_732_, v___x_743_, v_env_731_, v_asyncMode_745_, v___x_746_);
lean_dec(v_asyncMode_745_);
v_newEntries_748_ = lean_ctor_get(v___x_747_, 1);
lean_inc_ref(v_newEntries_748_);
lean_dec(v___x_747_);
v___x_749_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_748_, v_declName_727_);
if (lean_obj_tag(v___x_749_) == 1)
{
lean_object* v___x_750_; 
lean_dec_ref(v_env_731_);
lean_dec(v_declName_727_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
else
{
lean_dec(v___x_749_);
goto v___jp_733_;
}
}
else
{
lean_object* v_val_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_779_; 
v_val_751_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_779_ == 0)
{
v___x_753_ = v___x_742_;
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_val_751_);
lean_dec(v___x_742_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_755_ = l_Lean_Meta_Simp_simprocDeclExt;
v___x_756_ = 0;
v___x_757_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_732_, v___x_755_, v_env_731_, v_val_751_, v___x_756_);
lean_dec(v_val_751_);
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = lean_array_get_size(v___x_757_);
v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec_ref(v___x_757_);
lean_del_object(v___x_753_);
goto v___jp_733_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_sub(v___x_759_, v___x_761_);
v___x_763_ = lean_nat_dec_le(v___x_758_, v___x_762_);
if (v___x_763_ == 0)
{
lean_dec(v___x_762_);
lean_dec_ref(v___x_757_);
lean_del_object(v___x_753_);
goto v___jp_733_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___closed__0));
lean_inc(v_declName_727_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v_declName_727_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg(v___x_757_, v___x_765_, v___x_758_, v___x_762_);
lean_dec_ref(v___x_765_);
lean_dec_ref(v___x_757_);
if (lean_obj_tag(v___x_766_) == 1)
{
lean_object* v_val_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_env_731_);
lean_dec(v_declName_727_);
v_val_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_778_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_val_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_778_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_keys_771_; lean_object* v___x_773_; 
v_keys_771_ = lean_ctor_get(v_val_767_, 1);
lean_inc_ref(v_keys_771_);
lean_dec(v_val_767_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v_keys_771_);
v___x_773_ = v___x_769_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_keys_771_);
v___x_773_ = v_reuseFailAlloc_777_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 0);
lean_ctor_set(v___x_753_, 0, v___x_773_);
v___x_775_ = v___x_753_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_dec(v___x_766_);
lean_del_object(v___x_753_);
goto v___jp_733_;
}
}
}
}
}
v___jp_733_:
{
lean_object* v___x_734_; lean_object* v_toEnvExtension_735_; lean_object* v_asyncMode_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_builtin_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_734_ = l_Lean_Meta_Simp_simprocDeclExt;
v_toEnvExtension_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc_ref(v_toEnvExtension_735_);
v_asyncMode_736_ = lean_ctor_get(v_toEnvExtension_735_, 2);
lean_inc(v_asyncMode_736_);
lean_dec_ref(v_toEnvExtension_735_);
v___x_737_ = lean_box(0);
v___x_738_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_732_, v___x_734_, v_env_731_, v_asyncMode_736_, v___x_737_);
lean_dec(v_asyncMode_736_);
v_builtin_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc_ref(v_builtin_739_);
lean_dec(v___x_738_);
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_739_, v_declName_727_);
lean_dec(v_declName_727_);
lean_dec_ref(v_builtin_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___boxed(lean_object* v_declName_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(v_declName_780_, v_a_781_);
lean_dec(v_a_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(lean_object* v_declName_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(v_declName_784_, v_a_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___boxed(lean_object* v_declName_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(v_declName_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0(lean_object* v_00_u03b2_794_, lean_object* v_m_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v_m_795_, v_a_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___boxed(lean_object* v_00_u03b2_798_, lean_object* v_m_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0(v_00_u03b2_798_, v_m_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_m_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1(lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___redArg(v_x_803_, v_x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1___boxed(lean_object* v_00_u03b2_806_, lean_object* v_x_807_, lean_object* v_x_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1(v_00_u03b2_806_, v_x_807_, v_x_808_);
lean_dec(v_x_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2(lean_object* v_as_810_, lean_object* v_k_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___redArg(v_as_810_, v_k_811_, v_x_812_, v_x_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2___boxed(lean_object* v_as_816_, lean_object* v_k_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v_x_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Array_binSearchAux___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__2(v_as_816_, v_k_817_, v_x_818_, v_x_819_, v_x_820_);
lean_dec_ref(v_k_817_);
lean_dec_ref(v_as_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0(lean_object* v_00_u03b2_822_, lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_823_, v_x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_826_, lean_object* v_a_827_, lean_object* v_x_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_826_, v_a_827_, v_x_828_);
lean_dec(v_x_828_);
lean_dec(v_a_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2(lean_object* v_00_u03b2_830_, lean_object* v_x_831_, size_t v_x_832_, lean_object* v_x_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_831_, v_x_832_, v_x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
size_t v_x_1647__boxed_839_; lean_object* v_res_840_; 
v_x_1647__boxed_839_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_840_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_835_, v_x_836_, v_x_1647__boxed_839_, v_x_838_);
lean_dec(v_x_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_841_, lean_object* v_keys_842_, lean_object* v_vals_843_, lean_object* v_heq_844_, lean_object* v_i_845_, lean_object* v_k_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_842_, v_vals_843_, v_i_845_, v_k_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_848_, lean_object* v_keys_849_, lean_object* v_vals_850_, lean_object* v_heq_851_, lean_object* v_i_852_, lean_object* v_k_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_848_, v_keys_849_, v_vals_850_, v_heq_851_, v_i_852_, v_k_853_);
lean_dec(v_k_853_);
lean_dec_ref(v_vals_850_);
lean_dec_ref(v_keys_849_);
return v_res_854_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg(lean_object* v_a_855_, lean_object* v_x_856_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
uint8_t v___x_857_; 
v___x_857_ = 0;
return v___x_857_;
}
else
{
lean_object* v_key_858_; lean_object* v_tail_859_; uint8_t v___x_860_; 
v_key_858_ = lean_ctor_get(v_x_856_, 0);
v_tail_859_ = lean_ctor_get(v_x_856_, 2);
v___x_860_ = lean_name_eq(v_key_858_, v_a_855_);
if (v___x_860_ == 0)
{
v_x_856_ = v_tail_859_;
goto _start;
}
else
{
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg___boxed(lean_object* v_a_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg(v_a_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec(v_a_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg(lean_object* v_m_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_buckets_868_; lean_object* v___x_869_; uint64_t v___y_871_; 
v_buckets_868_ = lean_ctor_get(v_m_866_, 1);
v___x_869_ = lean_array_get_size(v_buckets_868_);
if (lean_obj_tag(v_a_867_) == 0)
{
uint64_t v___x_885_; 
v___x_885_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_871_ = v___x_885_;
goto v___jp_870_;
}
else
{
uint64_t v_hash_886_; 
v_hash_886_ = lean_ctor_get_uint64(v_a_867_, sizeof(void*)*2);
v___y_871_ = v_hash_886_;
goto v___jp_870_;
}
v___jp_870_:
{
uint64_t v___x_872_; uint64_t v___x_873_; uint64_t v_fold_874_; uint64_t v___x_875_; uint64_t v___x_876_; uint64_t v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_872_ = 32ULL;
v___x_873_ = lean_uint64_shift_right(v___y_871_, v___x_872_);
v_fold_874_ = lean_uint64_xor(v___y_871_, v___x_873_);
v___x_875_ = 16ULL;
v___x_876_ = lean_uint64_shift_right(v_fold_874_, v___x_875_);
v___x_877_ = lean_uint64_xor(v_fold_874_, v___x_876_);
v___x_878_ = lean_uint64_to_usize(v___x_877_);
v___x_879_ = lean_usize_of_nat(v___x_869_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_sub(v___x_879_, v___x_880_);
v___x_882_ = lean_usize_land(v___x_878_, v___x_881_);
v___x_883_ = lean_array_uget_borrowed(v_buckets_868_, v___x_882_);
v___x_884_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg(v_a_867_, v___x_883_);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg___boxed(lean_object* v_m_887_, lean_object* v_a_888_){
_start:
{
uint8_t v_res_889_; lean_object* v_r_890_; 
v_res_889_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg(v_m_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_m_887_);
v_r_890_ = lean_box(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object* v_declName_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; lean_object* v_env_895_; lean_object* v___x_896_; lean_object* v_toEnvExtension_897_; lean_object* v_asyncMode_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_builtin_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_894_ = lean_st_ref_get(v_a_892_);
v_env_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_env_895_);
lean_dec(v___x_894_);
v___x_896_ = l_Lean_Meta_Simp_simprocDeclExt;
v_toEnvExtension_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_ref(v_toEnvExtension_897_);
v_asyncMode_898_ = lean_ctor_get(v_toEnvExtension_897_, 2);
lean_inc(v_asyncMode_898_);
lean_dec_ref(v_toEnvExtension_897_);
v___x_899_ = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default;
v___x_900_ = lean_box(0);
v___x_901_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_899_, v___x_896_, v_env_895_, v_asyncMode_898_, v___x_900_);
lean_dec(v_asyncMode_898_);
v_builtin_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc_ref(v_builtin_902_);
lean_dec(v___x_901_);
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg(v_builtin_902_, v_declName_891_);
lean_dec_ref(v_builtin_902_);
v___x_904_ = lean_box(v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg___boxed(lean_object* v_declName_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec(v_declName_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object* v_declName_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_910_, v_a_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___boxed(lean_object* v_declName_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_Meta_Simp_isBuiltinSimproc(v_declName_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_declName_915_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0(lean_object* v_00_u03b2_920_, lean_object* v_m_921_, lean_object* v_a_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg(v_m_921_, v_a_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___boxed(lean_object* v_00_u03b2_924_, lean_object* v_m_925_, lean_object* v_a_926_){
_start:
{
uint8_t v_res_927_; lean_object* v_r_928_; 
v_res_927_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0(v_00_u03b2_924_, v_m_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_m_925_);
v_r_928_ = lean_box(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0(lean_object* v_00_u03b2_929_, lean_object* v_a_930_, lean_object* v_x_931_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg(v_a_930_, v_x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_933_, lean_object* v_a_934_, lean_object* v_x_935_){
_start:
{
uint8_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0(v_00_u03b2_933_, v_a_934_, v_x_935_);
lean_dec(v_x_935_);
lean_dec(v_a_934_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object* v_declName_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_941_; lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_956_; 
v___x_941_ = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(v_declName_938_, v_a_939_);
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_956_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
if (lean_obj_tag(v_a_942_) == 0)
{
uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_946_ = 0;
v___x_947_ = lean_box(v___x_946_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
lean_dec_ref(v_a_942_);
v___x_951_ = 1;
v___x_952_ = lean_box(v___x_951_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_952_);
v___x_954_ = v___x_944_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg___boxed(lean_object* v_declName_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_957_, v_a_958_);
lean_dec(v_a_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc(lean_object* v_declName_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_961_, v_a_963_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___boxed(lean_object* v_declName_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Meta_Simp_isSimproc(v_declName_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1___redArg(lean_object* v_a_971_, lean_object* v_b_972_, lean_object* v_x_973_){
_start:
{
if (lean_obj_tag(v_x_973_) == 0)
{
lean_dec(v_b_972_);
lean_dec(v_a_971_);
return v_x_973_;
}
else
{
lean_object* v_key_974_; lean_object* v_value_975_; lean_object* v_tail_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_988_; 
v_key_974_ = lean_ctor_get(v_x_973_, 0);
v_value_975_ = lean_ctor_get(v_x_973_, 1);
v_tail_976_ = lean_ctor_get(v_x_973_, 2);
v_isSharedCheck_988_ = !lean_is_exclusive(v_x_973_);
if (v_isSharedCheck_988_ == 0)
{
v___x_978_ = v_x_973_;
v_isShared_979_ = v_isSharedCheck_988_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_tail_976_);
lean_inc(v_value_975_);
lean_inc(v_key_974_);
lean_dec(v_x_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_988_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
uint8_t v___x_980_; 
v___x_980_ = lean_name_eq(v_key_974_, v_a_971_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1___redArg(v_a_971_, v_b_972_, v_tail_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 2, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_key_974_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_value_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
else
{
lean_object* v___x_986_; 
lean_dec(v_value_975_);
lean_dec(v_key_974_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_b_972_);
lean_ctor_set(v___x_978_, 0, v_a_971_);
v___x_986_ = v___x_978_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_971_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_b_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_tail_976_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
if (lean_obj_tag(v_x_990_) == 0)
{
return v_x_989_;
}
else
{
lean_object* v_key_991_; lean_object* v_value_992_; lean_object* v_tail_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1019_; 
v_key_991_ = lean_ctor_get(v_x_990_, 0);
v_value_992_ = lean_ctor_get(v_x_990_, 1);
v_tail_993_ = lean_ctor_get(v_x_990_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_x_990_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_995_ = v_x_990_;
v_isShared_996_ = v_isSharedCheck_1019_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_tail_993_);
lean_inc(v_value_992_);
lean_inc(v_key_991_);
lean_dec(v_x_990_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1019_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; uint64_t v___y_999_; 
v___x_997_ = lean_array_get_size(v_x_989_);
if (lean_obj_tag(v_key_991_) == 0)
{
uint64_t v___x_1017_; 
v___x_1017_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_999_ = v___x_1017_;
goto v___jp_998_;
}
else
{
uint64_t v_hash_1018_; 
v_hash_1018_ = lean_ctor_get_uint64(v_key_991_, sizeof(void*)*2);
v___y_999_ = v_hash_1018_;
goto v___jp_998_;
}
v___jp_998_:
{
uint64_t v___x_1000_; uint64_t v___x_1001_; uint64_t v_fold_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1000_ = 32ULL;
v___x_1001_ = lean_uint64_shift_right(v___y_999_, v___x_1000_);
v_fold_1002_ = lean_uint64_xor(v___y_999_, v___x_1001_);
v___x_1003_ = 16ULL;
v___x_1004_ = lean_uint64_shift_right(v_fold_1002_, v___x_1003_);
v___x_1005_ = lean_uint64_xor(v_fold_1002_, v___x_1004_);
v___x_1006_ = lean_uint64_to_usize(v___x_1005_);
v___x_1007_ = lean_usize_of_nat(v___x_997_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_sub(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_usize_land(v___x_1006_, v___x_1009_);
v___x_1011_ = lean_array_uget_borrowed(v_x_989_, v___x_1010_);
lean_inc(v___x_1011_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 2, v___x_1011_);
v___x_1013_ = v___x_995_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_key_991_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_value_992_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_array_uset(v_x_989_, v___x_1010_, v___x_1013_);
v_x_989_ = v___x_1014_;
v_x_990_ = v_tail_993_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1___redArg(lean_object* v_i_1020_, lean_object* v_source_1021_, lean_object* v_target_1022_){
_start:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_array_get_size(v_source_1021_);
v___x_1024_ = lean_nat_dec_lt(v_i_1020_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec_ref(v_source_1021_);
lean_dec(v_i_1020_);
return v_target_1022_;
}
else
{
lean_object* v_es_1025_; lean_object* v___x_1026_; lean_object* v_source_1027_; lean_object* v_target_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_es_1025_ = lean_array_fget(v_source_1021_, v_i_1020_);
v___x_1026_ = lean_box(0);
v_source_1027_ = lean_array_fset(v_source_1021_, v_i_1020_, v___x_1026_);
v_target_1028_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1_spec__2___redArg(v_target_1022_, v_es_1025_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_add(v_i_1020_, v___x_1029_);
lean_dec(v_i_1020_);
v_i_1020_ = v___x_1030_;
v_source_1021_ = v_source_1027_;
v_target_1022_ = v_target_1028_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0___redArg(lean_object* v_data_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_nbuckets_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1033_ = lean_array_get_size(v_data_1032_);
v___x_1034_ = lean_unsigned_to_nat(2u);
v_nbuckets_1035_ = lean_nat_mul(v___x_1033_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_mk_array(v_nbuckets_1035_, v___x_1037_);
v___x_1039_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1___redArg(v___x_1036_, v_data_1032_, v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(lean_object* v_m_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_){
_start:
{
lean_object* v_size_1043_; lean_object* v_buckets_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1090_; 
v_size_1043_ = lean_ctor_get(v_m_1040_, 0);
v_buckets_1044_ = lean_ctor_get(v_m_1040_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_m_1040_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1046_ = v_m_1040_;
v_isShared_1047_ = v_isSharedCheck_1090_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_buckets_1044_);
lean_inc(v_size_1043_);
lean_dec(v_m_1040_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1090_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; uint64_t v___y_1050_; 
v___x_1048_ = lean_array_get_size(v_buckets_1044_);
if (lean_obj_tag(v_a_1041_) == 0)
{
uint64_t v___x_1088_; 
v___x_1088_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1050_ = v___x_1088_;
goto v___jp_1049_;
}
else
{
uint64_t v_hash_1089_; 
v_hash_1089_ = lean_ctor_get_uint64(v_a_1041_, sizeof(void*)*2);
v___y_1050_ = v_hash_1089_;
goto v___jp_1049_;
}
v___jp_1049_:
{
uint64_t v___x_1051_; uint64_t v___x_1052_; uint64_t v_fold_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; lean_object* v_bkt_1062_; uint8_t v___x_1063_; 
v___x_1051_ = 32ULL;
v___x_1052_ = lean_uint64_shift_right(v___y_1050_, v___x_1051_);
v_fold_1053_ = lean_uint64_xor(v___y_1050_, v___x_1052_);
v___x_1054_ = 16ULL;
v___x_1055_ = lean_uint64_shift_right(v_fold_1053_, v___x_1054_);
v___x_1056_ = lean_uint64_xor(v_fold_1053_, v___x_1055_);
v___x_1057_ = lean_uint64_to_usize(v___x_1056_);
v___x_1058_ = lean_usize_of_nat(v___x_1048_);
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_sub(v___x_1058_, v___x_1059_);
v___x_1061_ = lean_usize_land(v___x_1057_, v___x_1060_);
v_bkt_1062_ = lean_array_uget_borrowed(v_buckets_1044_, v___x_1061_);
v___x_1063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0_spec__0___redArg(v_a_1041_, v_bkt_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v_size_x27_1065_; lean_object* v___x_1066_; lean_object* v_buckets_x27_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1064_ = lean_unsigned_to_nat(1u);
v_size_x27_1065_ = lean_nat_add(v_size_1043_, v___x_1064_);
lean_dec(v_size_1043_);
lean_inc(v_bkt_1062_);
v___x_1066_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1066_, 0, v_a_1041_);
lean_ctor_set(v___x_1066_, 1, v_b_1042_);
lean_ctor_set(v___x_1066_, 2, v_bkt_1062_);
v_buckets_x27_1067_ = lean_array_uset(v_buckets_1044_, v___x_1061_, v___x_1066_);
v___x_1068_ = lean_unsigned_to_nat(4u);
v___x_1069_ = lean_nat_mul(v_size_x27_1065_, v___x_1068_);
v___x_1070_ = lean_unsigned_to_nat(3u);
v___x_1071_ = lean_nat_div(v___x_1069_, v___x_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_array_get_size(v_buckets_x27_1067_);
v___x_1073_ = lean_nat_dec_le(v___x_1071_, v___x_1072_);
lean_dec(v___x_1071_);
if (v___x_1073_ == 0)
{
lean_object* v_val_1074_; lean_object* v___x_1076_; 
v_val_1074_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0___redArg(v_buckets_x27_1067_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_val_1074_);
lean_ctor_set(v___x_1046_, 0, v_size_x27_1065_);
v___x_1076_ = v___x_1046_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_size_x27_1065_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_val_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1079_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v_buckets_x27_1067_);
lean_ctor_set(v___x_1046_, 0, v_size_x27_1065_);
v___x_1079_ = v___x_1046_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_size_x27_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_buckets_x27_1067_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
else
{
lean_object* v___x_1081_; lean_object* v_buckets_x27_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
lean_inc(v_bkt_1062_);
v___x_1081_ = lean_box(0);
v_buckets_x27_1082_ = lean_array_uset(v_buckets_1044_, v___x_1061_, v___x_1081_);
v___x_1083_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1___redArg(v_a_1041_, v_b_1042_, v_bkt_1062_);
v___x_1084_ = lean_array_uset(v_buckets_x27_1082_, v___x_1061_, v___x_1083_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1084_);
v___x_1086_ = v___x_1046_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_size_1043_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__0));
v___x_1093_ = lean_mk_io_user_error(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore(lean_object* v_declName_1096_, lean_object* v_key_1097_, lean_object* v_proc_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_initializing();
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1140_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1140_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1140_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_unbox(v_a_1101_);
lean_dec(v_a_1101_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec_ref(v_proc_1098_);
lean_dec_ref(v_key_1097_);
lean_dec(v_declName_1096_);
v___x_1106_ = lean_obj_once(&l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1, &l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1_once, _init_l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__1);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v_keys_1112_; uint8_t v___x_1113_; 
v___x_1110_ = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
v___x_1111_ = lean_st_ref_get(v___x_1110_);
v_keys_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_keys_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Simp_isBuiltinSimproc_spec__0___redArg(v_keys_1112_, v_declName_1096_);
lean_dec_ref(v_keys_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v_keys_1115_; lean_object* v_procs_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1129_; 
v___x_1114_ = lean_st_ref_take(v___x_1110_);
v_keys_1115_ = lean_ctor_get(v___x_1114_, 0);
v_procs_1116_ = lean_ctor_get(v___x_1114_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1118_ = v___x_1114_;
v_isShared_1119_ = v_isSharedCheck_1129_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_procs_1116_);
lean_inc(v_keys_1115_);
lean_dec(v___x_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1129_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_inc(v_declName_1096_);
v___x_1120_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(v_keys_1115_, v_declName_1096_, v_key_1097_);
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(v_procs_1116_, v_declName_1096_, v_proc_1098_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v___x_1121_);
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_st_ref_set(v___x_1110_, v___x_1123_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1124_);
v___x_1126_ = v___x_1103_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec_ref(v_proc_1098_);
lean_dec_ref(v_key_1097_);
v___x_1130_ = ((lean_object*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__2));
v___x_1131_ = l_Lean_privateToUserName(v_declName_1096_);
v___x_1132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1131_, v___x_1113_);
v___x_1133_ = lean_string_append(v___x_1130_, v___x_1132_);
lean_dec_ref(v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___closed__3));
v___x_1135_ = lean_string_append(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_mk_io_user_error(v___x_1135_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 1);
lean_ctor_set(v___x_1103_, 0, v___x_1136_);
v___x_1138_ = v___x_1103_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec_ref(v_proc_1098_);
lean_dec_ref(v_key_1097_);
lean_dec(v_declName_1096_);
v_a_1141_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1100_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1100_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___boxed(lean_object* v_declName_1149_, lean_object* v_key_1150_, lean_object* v_proc_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_Simp_registerBuiltinSimprocCore(v_declName_1149_, v_key_1150_, v_proc_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0(lean_object* v_00_u03b2_1154_, lean_object* v_m_1155_, lean_object* v_a_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(v_m_1155_, v_a_1156_, v_b_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0(lean_object* v_00_u03b2_1159_, lean_object* v_data_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0___redArg(v_data_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1(lean_object* v_00_u03b2_1162_, lean_object* v_a_1163_, lean_object* v_b_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__1___redArg(v_a_1163_, v_b_1164_, v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1167_, lean_object* v_i_1168_, lean_object* v_source_1169_, lean_object* v_target_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1___redArg(v_i_1168_, v_source_1169_, v_target_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1173_, v_x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object* v_declName_1176_, lean_object* v_key_1177_, lean_object* v_proc_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_proc_1178_);
v___x_1181_ = l_Lean_Meta_Simp_registerBuiltinSimprocCore(v_declName_1176_, v_key_1177_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc___boxed(lean_object* v_declName_1182_, lean_object* v_key_1183_, lean_object* v_proc_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v_declName_1182_, v_key_1183_, v_proc_1184_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object* v_declName_1187_, lean_object* v_key_1188_, lean_object* v_proc_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_proc_1189_);
v___x_1192_ = l_Lean_Meta_Simp_registerBuiltinSimprocCore(v_declName_1187_, v_key_1188_, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc___boxed(lean_object* v_declName_1193_, lean_object* v_key_1194_, lean_object* v_proc_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v_declName_1193_, v_key_1194_, v_proc_1195_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lam__0(lean_object* v_declName_1198_, lean_object* v_keys_1199_, lean_object* v_s_1200_){
_start:
{
lean_object* v_builtin_1201_; lean_object* v_newEntries_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
v_builtin_1201_ = lean_ctor_get(v_s_1200_, 0);
v_newEntries_1202_ = lean_ctor_get(v_s_1200_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_s_1200_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1204_ = v_s_1200_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_newEntries_1202_);
lean_inc(v_builtin_1201_);
lean_dec(v_s_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(v_newEntries_1202_, v_declName_1198_, v_keys_1199_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_builtin_1201_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__0);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
lean_ctor_set(v___x_1216_, 3, v___x_1214_);
lean_ctor_set(v___x_1216_, 4, v___x_1214_);
lean_ctor_set(v___x_1216_, 5, v___x_1214_);
lean_ctor_set(v___x_1216_, 6, v___x_1214_);
lean_ctor_set(v___x_1216_, 7, v___x_1214_);
lean_ctor_set(v___x_1216_, 8, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(32u);
v___x_1218_ = lean_mk_empty_array_with_capacity(v___x_1217_);
v___x_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1220_ = ((size_t)5ULL);
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_unsigned_to_nat(32u);
v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1222_);
v___x_1224_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__3);
v___x_1225_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v___x_1223_);
lean_ctor_set(v___x_1225_, 2, v___x_1221_);
lean_ctor_set(v___x_1225_, 3, v___x_1221_);
lean_ctor_set_usize(v___x_1225_, 4, v___x_1220_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = lean_box(1);
v___x_1227_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4);
v___x_1228_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1);
v___x_1229_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v___x_1227_);
lean_ctor_set(v___x_1229_, 2, v___x_1226_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0(lean_object* v_msgData_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; lean_object* v_env_1235_; lean_object* v_options_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1234_ = lean_st_ref_get(v___y_1232_);
v_env_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc_ref(v_env_1235_);
lean_dec(v___x_1234_);
v_options_1236_ = lean_ctor_get(v___y_1231_, 2);
v___x_1237_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2);
v___x_1238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1236_);
v___x_1239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1239_, 0, v_env_1235_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
lean_ctor_set(v___x_1239_, 3, v_options_1236_);
v___x_1240_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_msgData_1230_);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___boxed(lean_object* v_msgData_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0(v_msgData_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(lean_object* v_msg_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_ref_1251_; lean_object* v___x_1252_; lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1261_; 
v_ref_1251_ = lean_ctor_get(v___y_1248_, 5);
v___x_1252_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0(v_msg_1247_, v___y_1248_, v___y_1249_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1261_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
lean_inc(v_ref_1251_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_ref_1251_);
lean_ctor_set(v___x_1257_, 1, v_a_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set_tag(v___x_1255_, 1);
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg___boxed(lean_object* v_msg_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v_msg_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1266_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__0(void){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__1(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__0, &l_Lean_Meta_Simp_registerSimproc___closed__0_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__0);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__2(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__1, &l_Lean_Meta_Simp_registerSimproc___closed__1_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__1);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1270_);
return v___x_1271_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__4(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l_Lean_Meta_Simp_registerSimproc___closed__3));
v___x_1274_ = l_Lean_stringToMessageData(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__6(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l_Lean_Meta_Simp_registerSimproc___closed__5));
v___x_1277_ = l_Lean_stringToMessageData(v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimproc___closed__8(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Simp_registerSimproc___closed__7));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object* v_declName_1281_, lean_object* v_keys_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1286_; lean_object* v_env_1287_; lean_object* v___f_1288_; lean_object* v___y_1290_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___x_1338_; 
v___x_1286_ = lean_st_ref_get(v_a_1284_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc_ref(v_env_1287_);
lean_dec(v___x_1286_);
lean_inc(v_declName_1281_);
v___f_1288_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerSimproc___lam__0), 3, 2);
lean_closure_set(v___f_1288_, 0, v_declName_1281_);
lean_closure_set(v___f_1288_, 1, v_keys_1282_);
v___x_1338_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1287_, v_declName_1281_);
lean_dec_ref(v_env_1287_);
if (lean_obj_tag(v___x_1338_) == 0)
{
v___y_1318_ = v_a_1283_;
v___y_1319_ = v_a_1284_;
goto v___jp_1317_;
}
else
{
uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec_ref(v___x_1338_);
lean_dec_ref(v___f_1288_);
v___x_1339_ = 0;
v___x_1340_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__4, &l_Lean_Meta_Simp_registerSimproc___closed__4_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__4);
v___x_1341_ = l_Lean_MessageData_ofConstName(v_declName_1281_, v___x_1339_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__8, &l_Lean_Meta_Simp_registerSimproc___closed__8_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__8);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_1344_, v_a_1283_, v_a_1284_);
return v___x_1345_;
}
v___jp_1289_:
{
lean_object* v___x_1291_; lean_object* v_env_1292_; lean_object* v_nextMacroScope_1293_; lean_object* v_ngen_1294_; lean_object* v_auxDeclNGen_1295_; lean_object* v_traceState_1296_; lean_object* v_messages_1297_; lean_object* v_infoState_1298_; lean_object* v_snapshotTasks_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1315_; 
v___x_1291_ = lean_st_ref_take(v___y_1290_);
v_env_1292_ = lean_ctor_get(v___x_1291_, 0);
v_nextMacroScope_1293_ = lean_ctor_get(v___x_1291_, 1);
v_ngen_1294_ = lean_ctor_get(v___x_1291_, 2);
v_auxDeclNGen_1295_ = lean_ctor_get(v___x_1291_, 3);
v_traceState_1296_ = lean_ctor_get(v___x_1291_, 4);
v_messages_1297_ = lean_ctor_get(v___x_1291_, 6);
v_infoState_1298_ = lean_ctor_get(v___x_1291_, 7);
v_snapshotTasks_1299_ = lean_ctor_get(v___x_1291_, 8);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v___x_1291_, 5);
lean_dec(v_unused_1316_);
v___x_1301_ = v___x_1291_;
v_isShared_1302_ = v_isSharedCheck_1315_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snapshotTasks_1299_);
lean_inc(v_infoState_1298_);
lean_inc(v_messages_1297_);
lean_inc(v_traceState_1296_);
lean_inc(v_auxDeclNGen_1295_);
lean_inc(v_ngen_1294_);
lean_inc(v_nextMacroScope_1293_);
lean_inc(v_env_1292_);
lean_dec(v___x_1291_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1315_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v_toEnvExtension_1304_; lean_object* v_asyncMode_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1303_ = l_Lean_Meta_Simp_simprocDeclExt;
v_toEnvExtension_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_ref(v_toEnvExtension_1304_);
v_asyncMode_1305_ = lean_ctor_get(v_toEnvExtension_1304_, 2);
lean_inc(v_asyncMode_1305_);
lean_dec_ref(v_toEnvExtension_1304_);
v___x_1306_ = lean_box(0);
v___x_1307_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_1303_, v_env_1292_, v___f_1288_, v_asyncMode_1305_, v___x_1306_);
lean_dec(v_asyncMode_1305_);
v___x_1308_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__2, &l_Lean_Meta_Simp_registerSimproc___closed__2_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__2);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 5, v___x_1308_);
lean_ctor_set(v___x_1301_, 0, v___x_1307_);
v___x_1310_ = v___x_1301_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_nextMacroScope_1293_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_ngen_1294_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_auxDeclNGen_1295_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_traceState_1296_);
lean_ctor_set(v_reuseFailAlloc_1314_, 5, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1314_, 6, v_messages_1297_);
lean_ctor_set(v_reuseFailAlloc_1314_, 7, v_infoState_1298_);
lean_ctor_set(v_reuseFailAlloc_1314_, 8, v_snapshotTasks_1299_);
v___x_1310_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_st_ref_set(v___y_1290_, v___x_1310_);
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
v___jp_1317_:
{
lean_object* v___x_1320_; 
lean_inc(v_declName_1281_);
v___x_1320_ = l_Lean_Meta_Simp_isSimproc___redArg(v_declName_1281_, v___y_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; uint8_t v___x_1322_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1320_);
v___x_1322_ = lean_unbox(v_a_1321_);
lean_dec(v_a_1321_);
if (v___x_1322_ == 0)
{
lean_dec(v_declName_1281_);
v___y_1290_ = v___y_1319_;
goto v___jp_1289_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v___f_1288_);
v___x_1323_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__4, &l_Lean_Meta_Simp_registerSimproc___closed__4_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__4);
v___x_1324_ = 0;
v___x_1325_ = l_Lean_MessageData_ofConstName(v_declName_1281_, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1323_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__6, &l_Lean_Meta_Simp_registerSimproc___closed__6_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__6);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_1328_, v___y_1318_, v___y_1319_);
return v___x_1329_;
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v___f_1288_);
lean_dec(v_declName_1281_);
v_a_1330_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1320_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1320_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___boxed(lean_object* v_declName_1346_, lean_object* v_keys_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Meta_Simp_registerSimproc(v_declName_1346_, v_keys_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0(lean_object* v_00_u03b1_1352_, lean_object* v_msg_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v_msg_1353_, v___y_1354_, v___y_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___boxed(lean_object* v_00_u03b1_1358_, lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0(v_00_u03b1_1358_, v_msg_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0(lean_object* v_e_u2081_1364_, lean_object* v_e_u2082_1365_){
_start:
{
lean_object* v_toSimprocOLeanEntry_1366_; lean_object* v_toSimprocOLeanEntry_1367_; lean_object* v_declName_1368_; lean_object* v_declName_1369_; uint8_t v___x_1370_; 
v_toSimprocOLeanEntry_1366_ = lean_ctor_get(v_e_u2081_1364_, 0);
v_toSimprocOLeanEntry_1367_ = lean_ctor_get(v_e_u2082_1365_, 0);
v_declName_1368_ = lean_ctor_get(v_toSimprocOLeanEntry_1366_, 0);
v_declName_1369_ = lean_ctor_get(v_toSimprocOLeanEntry_1367_, 0);
v___x_1370_ = lean_name_eq(v_declName_1368_, v_declName_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0___boxed(lean_object* v_e_u2081_1371_, lean_object* v_e_u2082_1372_){
_start:
{
uint8_t v_res_1373_; lean_object* v_r_1374_; 
v_res_1373_ = l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0(v_e_u2081_1371_, v_e_u2082_1372_);
lean_dec_ref(v_e_u2082_1372_);
lean_dec_ref(v_e_u2081_1371_);
v_r_1374_ = lean_box(v_res_1373_);
return v_r_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry___lam__0(lean_object* v_e_1377_){
_start:
{
lean_object* v_toSimprocOLeanEntry_1378_; lean_object* v_declName_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_toSimprocOLeanEntry_1378_ = lean_ctor_get(v_e_1377_, 0);
lean_inc_ref(v_toSimprocOLeanEntry_1378_);
lean_dec_ref(v_e_1377_);
v_declName_1379_ = lean_ctor_get(v_toSimprocOLeanEntry_1378_, 0);
lean_inc(v_declName_1379_);
lean_dec_ref(v_toSimprocOLeanEntry_1378_);
v___x_1380_ = 1;
v___x_1381_ = l_Lean_Name_toString(v_declName_1379_, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1_spec__2(lean_object* v_xs_1385_, lean_object* v_v_1386_, lean_object* v_i_1387_){
_start:
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = lean_array_get_size(v_xs_1385_);
v___x_1389_ = lean_nat_dec_lt(v_i_1387_, v___x_1388_);
if (v___x_1389_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_i_1387_);
v___x_1390_ = lean_box(0);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = lean_array_fget_borrowed(v_xs_1385_, v_i_1387_);
v___x_1392_ = lean_name_eq(v___x_1391_, v_v_1386_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_unsigned_to_nat(1u);
v___x_1394_ = lean_nat_add(v_i_1387_, v___x_1393_);
lean_dec(v_i_1387_);
v_i_1387_ = v___x_1394_;
goto _start;
}
else
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_i_1387_);
return v___x_1396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_xs_1397_, lean_object* v_v_1398_, lean_object* v_i_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1_spec__2(v_xs_1397_, v_v_1398_, v_i_1399_);
lean_dec(v_v_1398_);
lean_dec_ref(v_xs_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1(lean_object* v_xs_1401_, lean_object* v_v_1402_){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1_spec__2(v_xs_1401_, v_v_1402_, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_1405_, lean_object* v_v_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1(v_xs_1405_, v_v_1406_);
lean_dec(v_v_1406_);
lean_dec_ref(v_xs_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg(lean_object* v_x_1408_, size_t v_x_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v_es_1411_; lean_object* v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; size_t v___x_1415_; lean_object* v_j_1416_; lean_object* v_entry_1417_; 
v_es_1411_ = lean_ctor_get(v_x_1408_, 0);
v___x_1412_ = lean_box(2);
v___x_1413_ = ((size_t)5ULL);
v___x_1414_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1415_ = lean_usize_land(v_x_1409_, v___x_1414_);
v_j_1416_ = lean_usize_to_nat(v___x_1415_);
v_entry_1417_ = lean_array_get(v___x_1412_, v_es_1411_, v_j_1416_);
switch(lean_obj_tag(v_entry_1417_))
{
case 0:
{
lean_object* v_key_1418_; uint8_t v___x_1419_; 
v_key_1418_ = lean_ctor_get(v_entry_1417_, 0);
lean_inc(v_key_1418_);
lean_dec_ref(v_entry_1417_);
v___x_1419_ = lean_name_eq(v_x_1410_, v_key_1418_);
lean_dec(v_key_1418_);
if (v___x_1419_ == 0)
{
lean_dec(v_j_1416_);
return v_x_1408_;
}
else
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1427_; 
lean_inc_ref(v_es_1411_);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_x_1408_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; 
v_unused_1428_ = lean_ctor_get(v_x_1408_, 0);
lean_dec(v_unused_1428_);
v___x_1421_ = v_x_1408_;
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v_x_1408_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1427_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_array_set(v_es_1411_, v_j_1416_, v___x_1412_);
lean_dec(v_j_1416_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1423_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
case 1:
{
lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1462_; 
lean_inc_ref(v_es_1411_);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_x_1408_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_x_1408_, 0);
lean_dec(v_unused_1463_);
v___x_1430_ = v_x_1408_;
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
else
{
lean_dec(v_x_1408_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1462_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v_node_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1461_; 
v_node_1432_ = lean_ctor_get(v_entry_1417_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_entry_1417_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1434_ = v_entry_1417_;
v_isShared_1435_ = v_isSharedCheck_1461_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_node_1432_);
lean_dec(v_entry_1417_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1461_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_entries_1436_; size_t v___x_1437_; lean_object* v_newNode_1438_; lean_object* v___x_1439_; 
v_entries_1436_ = lean_array_set(v_es_1411_, v_j_1416_, v___x_1412_);
v___x_1437_ = lean_usize_shift_right(v_x_1409_, v___x_1413_);
v_newNode_1438_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg(v_node_1432_, v___x_1437_, v_x_1410_);
lean_inc_ref(v_newNode_1438_);
v___x_1439_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1441_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v_newNode_1438_);
v___x_1441_ = v___x_1434_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_newNode_1438_);
v___x_1441_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_array_set(v_entries_1436_, v_j_1416_, v___x_1441_);
lean_dec(v_j_1416_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1442_);
v___x_1444_ = v___x_1430_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_val_1447_; lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_newNode_1438_);
lean_del_object(v___x_1434_);
v_val_1447_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_val_1447_);
lean_dec_ref(v___x_1439_);
v_fst_1448_ = lean_ctor_get(v_val_1447_, 0);
v_snd_1449_ = lean_ctor_get(v_val_1447_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_val_1447_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v_val_1447_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1449_);
lean_inc(v_fst_1448_);
lean_dec(v_val_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_fst_1448_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_snd_1449_);
v___x_1454_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1455_ = lean_array_set(v_entries_1436_, v_j_1416_, v___x_1454_);
lean_dec(v_j_1416_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1455_);
v___x_1457_ = v___x_1430_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1416_);
return v_x_1408_;
}
}
}
else
{
lean_object* v_ks_1464_; lean_object* v_vs_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1479_; 
v_ks_1464_ = lean_ctor_get(v_x_1408_, 0);
v_vs_1465_ = lean_ctor_get(v_x_1408_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_x_1408_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1467_ = v_x_1408_;
v_isShared_1468_ = v_isSharedCheck_1479_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_vs_1465_);
lean_inc(v_ks_1464_);
lean_dec(v_x_1408_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1479_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0_spec__1(v_ks_1464_, v_x_1410_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1471_; 
if (v_isShared_1468_ == 0)
{
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_ks_1464_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_vs_1465_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
else
{
lean_object* v_val_1473_; lean_object* v_keys_x27_1474_; lean_object* v_vals_x27_1475_; lean_object* v___x_1477_; 
v_val_1473_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_val_1473_);
lean_dec_ref(v___x_1469_);
lean_inc(v_val_1473_);
v_keys_x27_1474_ = l_Array_eraseIdx___redArg(v_ks_1464_, v_val_1473_);
v_vals_x27_1475_ = l_Array_eraseIdx___redArg(v_vs_1465_, v_val_1473_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 1, v_vals_x27_1475_);
lean_ctor_set(v___x_1467_, 0, v_keys_x27_1474_);
v___x_1477_ = v___x_1467_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_keys_x27_1474_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_vals_x27_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg___boxed(lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_x_1482_){
_start:
{
size_t v_x_197__boxed_1483_; lean_object* v_res_1484_; 
v_x_197__boxed_1483_ = lean_unbox_usize(v_x_1481_);
lean_dec(v_x_1481_);
v_res_1484_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg(v_x_1480_, v_x_197__boxed_1483_, v_x_1482_);
lean_dec(v_x_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg(lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
uint64_t v___y_1488_; 
if (lean_obj_tag(v_x_1486_) == 0)
{
uint64_t v___x_1491_; 
v___x_1491_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1488_ = v___x_1491_;
goto v___jp_1487_;
}
else
{
uint64_t v_hash_1492_; 
v_hash_1492_ = lean_ctor_get_uint64(v_x_1486_, sizeof(void*)*2);
v___y_1488_ = v_hash_1492_;
goto v___jp_1487_;
}
v___jp_1487_:
{
size_t v_h_1489_; lean_object* v___x_1490_; 
v_h_1489_ = lean_uint64_to_usize(v___y_1488_);
v___x_1490_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg(v_x_1485_, v_h_1489_, v_x_1486_);
return v___x_1490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg___boxed(lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg(v_x_1493_, v_x_1494_);
lean_dec(v_x_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object* v_s_1496_, lean_object* v_declName_1497_){
_start:
{
lean_object* v_pre_1498_; lean_object* v_post_1499_; lean_object* v_simprocNames_1500_; lean_object* v_erased_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1511_; 
v_pre_1498_ = lean_ctor_get(v_s_1496_, 0);
v_post_1499_ = lean_ctor_get(v_s_1496_, 1);
v_simprocNames_1500_ = lean_ctor_get(v_s_1496_, 2);
v_erased_1501_ = lean_ctor_get(v_s_1496_, 3);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_s_1496_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1503_ = v_s_1496_;
v_isShared_1504_ = v_isSharedCheck_1511_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_erased_1501_);
lean_inc(v_simprocNames_1500_);
lean_inc(v_post_1499_);
lean_inc(v_pre_1498_);
lean_dec(v_s_1496_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1511_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1505_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg(v_simprocNames_1500_, v_declName_1497_);
v___x_1506_ = lean_box(0);
v___x_1507_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(v_erased_1501_, v_declName_1497_, v___x_1506_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 3, v___x_1507_);
lean_ctor_set(v___x_1503_, 2, v___x_1505_);
v___x_1509_ = v___x_1503_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_pre_1498_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_post_1499_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0(lean_object* v_00_u03b2_1512_, lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg(v_x_1513_, v_x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___boxed(lean_object* v_00_u03b2_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0(v_00_u03b2_1516_, v_x_1517_, v_x_1518_);
lean_dec(v_x_1518_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0(lean_object* v_00_u03b2_1520_, lean_object* v_x_1521_, size_t v_x_1522_, lean_object* v_x_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___redArg(v_x_1521_, v_x_1522_, v_x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_){
_start:
{
size_t v_x_380__boxed_1529_; lean_object* v_res_1530_; 
v_x_380__boxed_1529_ = lean_unbox_usize(v_x_1527_);
lean_dec(v_x_1527_);
v_res_1530_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0_spec__0(v_00_u03b2_1525_, v_x_1526_, v_x_380__boxed_1529_, v_x_1528_);
lean_dec(v_x_1528_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__0);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0___closed__1);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_1539_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_1540_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
lean_ctor_set(v___x_1540_, 2, v___x_1538_);
lean_ctor_set(v___x_1540_, 3, v___x_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_1543_ = lean_st_mk_ref(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2____boxed(lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_();
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1207380286____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_1549_ = lean_st_mk_ref(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1207380286____hygCtx___hyg_2____boxed(lean_object* v_a_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1207380286____hygCtx___hyg_2_();
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg(lean_object* v_e_1553_){
_start:
{
if (lean_obj_tag(v_e_1553_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1563_; 
v_a_1555_ = lean_ctor_get(v_e_1553_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v_e_1553_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1557_ = v_e_1553_;
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v_e_1553_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = lean_mk_io_user_error(v_a_1555_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 1);
lean_ctor_set(v___x_1557_, 0, v___x_1559_);
v___x_1561_ = v___x_1557_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_a_1564_ = lean_ctor_get(v_e_1553_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_e_1553_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v_e_1553_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v_e_1553_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 0);
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg(v_e_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0(lean_object* v_00_u03b1_1575_, lean_object* v_e_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg(v_e_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_e_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0(v_00_u03b1_1579_, v_e_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl(lean_object* v_declName_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_env_1592_; lean_object* v_opts_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; 
v_env_1592_ = lean_ctor_get(v_a_1590_, 0);
lean_inc_ref(v_env_1592_);
v_opts_1593_ = lean_ctor_get(v_a_1590_, 1);
lean_inc_ref(v_opts_1593_);
lean_dec_ref(v_a_1590_);
v___x_1594_ = 0;
lean_inc(v_declName_1589_);
lean_inc_ref(v_env_1592_);
v___x_1595_ = l_Lean_Environment_find_x3f(v_env_1592_, v_declName_1589_, v___x_1594_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; uint8_t v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
v___x_1596_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__0));
v___x_1597_ = 1;
v___x_1598_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_1589_, v___x_1597_);
v___x_1599_ = lean_string_append(v___x_1596_, v___x_1598_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1));
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
v___x_1602_ = lean_mk_io_user_error(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
return v___x_1603_;
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1683_; 
v_val_1604_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1606_ = v___x_1595_;
v_isShared_1607_ = v_isSharedCheck_1683_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_val_1604_);
lean_dec(v___x_1595_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1683_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_ConstantInfo_type(v_val_1604_);
if (lean_obj_tag(v___x_1625_) == 4)
{
lean_object* v_declName_1626_; 
v_declName_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_declName_1626_);
lean_dec_ref(v___x_1625_);
if (lean_obj_tag(v_declName_1626_) == 1)
{
lean_object* v_pre_1627_; 
v_pre_1627_ = lean_ctor_get(v_declName_1626_, 0);
lean_inc(v_pre_1627_);
if (lean_obj_tag(v_pre_1627_) == 1)
{
lean_object* v_pre_1628_; 
v_pre_1628_ = lean_ctor_get(v_pre_1627_, 0);
lean_inc(v_pre_1628_);
if (lean_obj_tag(v_pre_1628_) == 1)
{
lean_object* v_pre_1629_; 
v_pre_1629_ = lean_ctor_get(v_pre_1628_, 0);
lean_inc(v_pre_1629_);
if (lean_obj_tag(v_pre_1629_) == 1)
{
lean_object* v_pre_1630_; 
v_pre_1630_ = lean_ctor_get(v_pre_1629_, 0);
if (lean_obj_tag(v_pre_1630_) == 0)
{
lean_object* v_str_1631_; lean_object* v_str_1632_; lean_object* v_str_1633_; lean_object* v_str_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v_str_1631_ = lean_ctor_get(v_declName_1626_, 1);
lean_inc_ref(v_str_1631_);
lean_dec_ref(v_declName_1626_);
v_str_1632_ = lean_ctor_get(v_pre_1627_, 1);
lean_inc_ref(v_str_1632_);
lean_dec_ref(v_pre_1627_);
v_str_1633_ = lean_ctor_get(v_pre_1628_, 1);
lean_inc_ref(v_str_1633_);
lean_dec_ref(v_pre_1628_);
v_str_1634_ = lean_ctor_get(v_pre_1629_, 1);
lean_inc_ref(v_str_1634_);
lean_dec_ref(v_pre_1629_);
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_1636_ = lean_string_dec_eq(v_str_1634_, v___x_1635_);
lean_dec_ref(v_str_1634_);
if (v___x_1636_ == 0)
{
lean_dec_ref(v_str_1633_);
lean_dec_ref(v_str_1632_);
lean_dec_ref(v_str_1631_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
else
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_1638_ = lean_string_dec_eq(v_str_1633_, v___x_1637_);
lean_dec_ref(v_str_1633_);
if (v___x_1638_ == 0)
{
lean_dec_ref(v_str_1632_);
lean_dec_ref(v_str_1631_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
else
{
lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_1640_ = lean_string_dec_eq(v_str_1632_, v___x_1639_);
lean_dec_ref(v_str_1632_);
if (v___x_1640_ == 0)
{
lean_dec_ref(v_str_1631_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
else
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4));
v___x_1642_ = lean_string_dec_eq(v_str_1631_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; uint8_t v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5));
v___x_1644_ = lean_string_dec_eq(v_str_1631_, v___x_1643_);
lean_dec_ref(v_str_1631_);
if (v___x_1644_ == 0)
{
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_del_object(v___x_1606_);
lean_dec(v_val_1604_);
v___x_1645_ = l_Lean_Environment_evalConst___redArg(v_env_1592_, v_opts_1593_, v_declName_1589_, v___x_1644_);
lean_dec(v_declName_1589_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
v___x_1646_ = l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg(v___x_1645_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v_a_1647_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1646_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1646_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec_ref(v_str_1631_);
lean_del_object(v___x_1606_);
lean_dec(v_val_1604_);
v___x_1664_ = l_Lean_Environment_evalConst___redArg(v_env_1592_, v_opts_1593_, v_declName_1589_, v___x_1642_);
lean_dec(v_declName_1589_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
v___x_1665_ = l_IO_ofExcept___at___00Lean_Meta_Simp_getSimprocFromDeclImpl_spec__0___redArg(v___x_1664_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1674_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1674_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1670_; lean_object* v___x_1672_; 
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1670_);
v___x_1672_ = v___x_1668_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1665_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1665_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
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
lean_dec_ref(v_pre_1629_);
lean_dec_ref(v_pre_1628_);
lean_dec_ref(v_pre_1627_);
lean_dec_ref(v_declName_1626_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
}
else
{
lean_dec_ref(v_pre_1628_);
lean_dec(v_pre_1629_);
lean_dec_ref(v_pre_1627_);
lean_dec_ref(v_declName_1626_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
}
else
{
lean_dec_ref(v_pre_1627_);
lean_dec(v_pre_1628_);
lean_dec_ref(v_declName_1626_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
}
else
{
lean_dec(v_pre_1627_);
lean_dec_ref(v_declName_1626_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
}
else
{
lean_dec(v_declName_1626_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
}
else
{
lean_dec_ref(v___x_1625_);
lean_dec_ref(v_opts_1593_);
lean_dec_ref(v_env_1592_);
goto v___jp_1608_;
}
v___jp_1608_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1609_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__2));
v___x_1610_ = l_Lean_privateToUserName(v_declName_1589_);
v___x_1611_ = 1;
v___x_1612_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1610_, v___x_1611_);
v___x_1613_ = lean_string_append(v___x_1609_, v___x_1612_);
lean_dec_ref(v___x_1612_);
v___x_1614_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__3));
v___x_1615_ = lean_string_append(v___x_1613_, v___x_1614_);
v___x_1616_ = l_Lean_ConstantInfo_type(v_val_1604_);
lean_dec(v_val_1604_);
v___x_1617_ = lean_expr_dbg_to_string(v___x_1616_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_string_append(v___x_1615_, v___x_1617_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1));
v___x_1620_ = lean_string_append(v___x_1618_, v___x_1619_);
v___x_1621_ = lean_mk_io_user_error(v___x_1620_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1621_);
v___x_1623_ = v___x_1606_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___boxed(lean_object* v_declName_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Meta_Simp_getSimprocFromDeclImpl(v_declName_1684_, v_a_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry(lean_object* v_e_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_declName_1691_; lean_object* v___x_1692_; 
v_declName_1691_ = lean_ctor_get(v_e_1688_, 0);
lean_inc_ref(v_a_1689_);
lean_inc(v_declName_1691_);
v___x_1692_ = l_Lean_Meta_Simp_getSimprocFromDeclImpl(v_declName_1691_, v_a_1689_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v___x_1692_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1692_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_e_1688_);
lean_ctor_set(v___x_1697_, 1, v_a_1693_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 0, v___x_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_e_1688_);
v_a_1702_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1692_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1692_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry___boxed(lean_object* v_e_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Simp_toSimprocEntry(v_e_1710_, v_a_1711_);
lean_dec_ref(v_a_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lam__0(lean_object* v_declName_1714_, lean_object* v_s_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_Meta_Simp_Simprocs_erase(v_s_1715_, v_declName_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1717_, lean_object* v_i_1718_, lean_object* v_k_1719_){
_start:
{
lean_object* v___x_1720_; uint8_t v___x_1721_; 
v___x_1720_ = lean_array_get_size(v_keys_1717_);
v___x_1721_ = lean_nat_dec_lt(v_i_1718_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_dec(v_i_1718_);
return v___x_1721_;
}
else
{
lean_object* v_k_x27_1722_; uint8_t v___x_1723_; 
v_k_x27_1722_ = lean_array_fget_borrowed(v_keys_1717_, v_i_1718_);
v___x_1723_ = lean_name_eq(v_k_1719_, v_k_x27_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_unsigned_to_nat(1u);
v___x_1725_ = lean_nat_add(v_i_1718_, v___x_1724_);
lean_dec(v_i_1718_);
v_i_1718_ = v___x_1725_;
goto _start;
}
else
{
lean_dec(v_i_1718_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1727_, lean_object* v_i_1728_, lean_object* v_k_1729_){
_start:
{
uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_res_1730_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_1727_, v_i_1728_, v_k_1729_);
lean_dec(v_k_1729_);
lean_dec_ref(v_keys_1727_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg(lean_object* v_x_1732_, size_t v_x_1733_, lean_object* v_x_1734_){
_start:
{
if (lean_obj_tag(v_x_1732_) == 0)
{
lean_object* v_es_1735_; lean_object* v___x_1736_; size_t v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v_j_1740_; lean_object* v___x_1741_; 
v_es_1735_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_es_1735_);
lean_dec_ref(v_x_1732_);
v___x_1736_ = lean_box(2);
v___x_1737_ = ((size_t)5ULL);
v___x_1738_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_1739_ = lean_usize_land(v_x_1733_, v___x_1738_);
v_j_1740_ = lean_usize_to_nat(v___x_1739_);
v___x_1741_ = lean_array_get(v___x_1736_, v_es_1735_, v_j_1740_);
lean_dec(v_j_1740_);
lean_dec_ref(v_es_1735_);
switch(lean_obj_tag(v___x_1741_))
{
case 0:
{
lean_object* v_key_1742_; uint8_t v___x_1743_; 
v_key_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_key_1742_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = lean_name_eq(v_x_1734_, v_key_1742_);
lean_dec(v_key_1742_);
return v___x_1743_;
}
case 1:
{
lean_object* v_node_1744_; size_t v___x_1745_; 
v_node_1744_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_node_1744_);
lean_dec_ref(v___x_1741_);
v___x_1745_ = lean_usize_shift_right(v_x_1733_, v___x_1737_);
v_x_1732_ = v_node_1744_;
v_x_1733_ = v___x_1745_;
goto _start;
}
default: 
{
uint8_t v___x_1747_; 
v___x_1747_ = 0;
return v___x_1747_;
}
}
}
else
{
lean_object* v_ks_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_ks_1748_ = lean_ctor_get(v_x_1732_, 0);
lean_inc_ref(v_ks_1748_);
lean_dec_ref(v_x_1732_);
v___x_1749_ = lean_unsigned_to_nat(0u);
v___x_1750_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_1748_, v___x_1749_, v_x_1734_);
lean_dec_ref(v_ks_1748_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
size_t v_x_554__boxed_1754_; uint8_t v_res_1755_; lean_object* v_r_1756_; 
v_x_554__boxed_1754_ = lean_unbox_usize(v_x_1752_);
lean_dec(v_x_1752_);
v_res_1755_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg(v_x_1751_, v_x_554__boxed_1754_, v_x_1753_);
lean_dec(v_x_1753_);
v_r_1756_ = lean_box(v_res_1755_);
return v_r_1756_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
uint64_t v___y_1760_; 
if (lean_obj_tag(v_x_1758_) == 0)
{
uint64_t v___x_1763_; 
v___x_1763_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1760_ = v___x_1763_;
goto v___jp_1759_;
}
else
{
uint64_t v_hash_1764_; 
v_hash_1764_ = lean_ctor_get_uint64(v_x_1758_, sizeof(void*)*2);
v___y_1760_ = v_hash_1764_;
goto v___jp_1759_;
}
v___jp_1759_:
{
size_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_uint64_to_usize(v___y_1760_);
v___x_1762_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg(v_x_1757_, v___x_1761_, v_x_1758_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg___boxed(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_x_1765_, v_x_1766_);
lean_dec(v_x_1766_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__1));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__2(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_Meta_Simp_eraseSimprocAttr___closed__1));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object* v_ext_1774_, lean_object* v_declName_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v_ext_1780_; lean_object* v_toEnvExtension_1781_; lean_object* v_env_1782_; lean_object* v_asyncMode_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v_simprocNames_1786_; lean_object* v___f_1787_; lean_object* v___y_1789_; uint8_t v___x_1812_; 
v___x_1779_ = lean_st_ref_get(v_a_1777_);
v_ext_1780_ = lean_ctor_get(v_ext_1774_, 1);
v_toEnvExtension_1781_ = lean_ctor_get(v_ext_1780_, 0);
v_env_1782_ = lean_ctor_get(v___x_1779_, 0);
lean_inc_ref(v_env_1782_);
lean_dec(v___x_1779_);
v_asyncMode_1783_ = lean_ctor_get(v_toEnvExtension_1781_, 2);
v___x_1784_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_1785_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1784_, v_ext_1774_, v_env_1782_, v_asyncMode_1783_);
v_simprocNames_1786_ = lean_ctor_get(v___x_1785_, 2);
lean_inc_ref(v_simprocNames_1786_);
lean_dec(v___x_1785_);
lean_inc(v_declName_1775_);
v___f_1787_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___lam__0), 2, 1);
lean_closure_set(v___f_1787_, 0, v_declName_1775_);
v___x_1812_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_simprocNames_1786_, v_declName_1775_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v___f_1787_);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_ext_1774_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; lean_object* v_unused_1826_; 
v_unused_1825_ = lean_ctor_get(v_ext_1774_, 1);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_ext_1774_, 0);
lean_dec(v_unused_1826_);
v___x_1814_ = v_ext_1774_;
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v_ext_1774_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1824_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1816_ = lean_obj_once(&l_Lean_Meta_Simp_eraseSimprocAttr___closed__0, &l_Lean_Meta_Simp_eraseSimprocAttr___closed__0_once, _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__0);
v___x_1817_ = l_Lean_MessageData_ofConstName(v_declName_1775_, v___x_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set_tag(v___x_1814_, 7);
lean_ctor_set(v___x_1814_, 1, v___x_1817_);
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1819_ = v___x_1814_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_obj_once(&l_Lean_Meta_Simp_eraseSimprocAttr___closed__2, &l_Lean_Meta_Simp_eraseSimprocAttr___closed__2_once, _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__2);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_1821_, v_a_1776_, v_a_1777_);
return v___x_1822_;
}
}
}
else
{
lean_dec(v_declName_1775_);
v___y_1789_ = v_a_1777_;
goto v___jp_1788_;
}
v___jp_1788_:
{
lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_traceState_1795_; lean_object* v_messages_1796_; lean_object* v_infoState_1797_; lean_object* v_snapshotTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1810_; 
v___x_1790_ = lean_st_ref_take(v___y_1789_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1790_, 1);
v_ngen_1793_ = lean_ctor_get(v___x_1790_, 2);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1790_, 3);
v_traceState_1795_ = lean_ctor_get(v___x_1790_, 4);
v_messages_1796_ = lean_ctor_get(v___x_1790_, 6);
v_infoState_1797_ = lean_ctor_get(v___x_1790_, 7);
v_snapshotTasks_1798_ = lean_ctor_get(v___x_1790_, 8);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v___x_1790_, 5);
lean_dec(v_unused_1811_);
v___x_1800_ = v___x_1790_;
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snapshotTasks_1798_);
lean_inc(v_infoState_1797_);
lean_inc(v_messages_1796_);
lean_inc(v_traceState_1795_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_inc(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1810_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1802_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1774_, v_env_1791_, v___f_1787_);
v___x_1803_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__2, &l_Lean_Meta_Simp_registerSimproc___closed__2_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__2);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 5, v___x_1803_);
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1809_, 6, v_messages_1796_);
lean_ctor_set(v_reuseFailAlloc_1809_, 7, v_infoState_1797_);
lean_ctor_set(v_reuseFailAlloc_1809_, 8, v_snapshotTasks_1798_);
v___x_1805_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_st_ref_set(v___y_1789_, v___x_1805_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___boxed(lean_object* v_ext_1827_, lean_object* v_declName_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Meta_Simp_eraseSimprocAttr(v_ext_1827_, v_declName_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1832_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0(lean_object* v_00_u03b2_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
uint8_t v___x_1836_; 
v___x_1836_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_x_1834_, v_x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___boxed(lean_object* v_00_u03b2_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0(v_00_u03b2_1837_, v_x_1838_, v_x_1839_);
lean_dec(v_x_1839_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0(lean_object* v_00_u03b2_1842_, lean_object* v_x_1843_, size_t v_x_1844_, lean_object* v_x_1845_){
_start:
{
uint8_t v___x_1846_; 
v___x_1846_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg(v_x_1843_, v_x_1844_, v_x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
size_t v_x_721__boxed_1851_; uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_x_721__boxed_1851_ = lean_unbox_usize(v_x_1849_);
lean_dec(v_x_1849_);
v_res_1852_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0(v_00_u03b2_1847_, v_x_1848_, v_x_721__boxed_1851_, v_x_1850_);
lean_dec(v_x_1850_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1854_, lean_object* v_keys_1855_, lean_object* v_vals_1856_, lean_object* v_heq_1857_, lean_object* v_i_1858_, lean_object* v_k_1859_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_1855_, v_i_1858_, v_k_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1861_, lean_object* v_keys_1862_, lean_object* v_vals_1863_, lean_object* v_heq_1864_, lean_object* v_i_1865_, lean_object* v_k_1866_){
_start:
{
uint8_t v_res_1867_; lean_object* v_r_1868_; 
v_res_1867_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_1861_, v_keys_1862_, v_vals_1863_, v_heq_1864_, v_i_1865_, v_k_1866_);
lean_dec(v_k_1866_);
lean_dec_ref(v_vals_1863_);
lean_dec_ref(v_keys_1862_);
v_r_1868_ = lean_box(v_res_1867_);
return v_r_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg(lean_object* v_ext_1869_, lean_object* v_b_1870_, uint8_t v_kind_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_currNamespace_1875_; lean_object* v___x_1876_; lean_object* v_env_1877_; lean_object* v_nextMacroScope_1878_; lean_object* v_ngen_1879_; lean_object* v_auxDeclNGen_1880_; lean_object* v_traceState_1881_; lean_object* v_messages_1882_; lean_object* v_infoState_1883_; lean_object* v_snapshotTasks_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v_currNamespace_1875_ = lean_ctor_get(v___y_1872_, 6);
lean_inc(v_currNamespace_1875_);
lean_dec_ref(v___y_1872_);
v___x_1876_ = lean_st_ref_take(v___y_1873_);
v_env_1877_ = lean_ctor_get(v___x_1876_, 0);
v_nextMacroScope_1878_ = lean_ctor_get(v___x_1876_, 1);
v_ngen_1879_ = lean_ctor_get(v___x_1876_, 2);
v_auxDeclNGen_1880_ = lean_ctor_get(v___x_1876_, 3);
v_traceState_1881_ = lean_ctor_get(v___x_1876_, 4);
v_messages_1882_ = lean_ctor_get(v___x_1876_, 6);
v_infoState_1883_ = lean_ctor_get(v___x_1876_, 7);
v_snapshotTasks_1884_ = lean_ctor_get(v___x_1876_, 8);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1876_, 5);
lean_dec(v_unused_1897_);
v___x_1886_ = v___x_1876_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_snapshotTasks_1884_);
lean_inc(v_infoState_1883_);
lean_inc(v_messages_1882_);
lean_inc(v_traceState_1881_);
lean_inc(v_auxDeclNGen_1880_);
lean_inc(v_ngen_1879_);
lean_inc(v_nextMacroScope_1878_);
lean_inc(v_env_1877_);
lean_dec(v___x_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___x_1888_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_1877_, v_ext_1869_, v_b_1870_, v_kind_1871_, v_currNamespace_1875_);
v___x_1889_ = lean_obj_once(&l_Lean_Meta_Simp_registerSimproc___closed__2, &l_Lean_Meta_Simp_registerSimproc___closed__2_once, _init_l_Lean_Meta_Simp_registerSimproc___closed__2);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 5, v___x_1889_);
lean_ctor_set(v___x_1886_, 0, v___x_1888_);
v___x_1891_ = v___x_1886_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_nextMacroScope_1878_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_ngen_1879_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_auxDeclNGen_1880_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v_traceState_1881_);
lean_ctor_set(v_reuseFailAlloc_1895_, 5, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1895_, 6, v_messages_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 7, v_infoState_1883_);
lean_ctor_set(v_reuseFailAlloc_1895_, 8, v_snapshotTasks_1884_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_st_ref_set(v___y_1873_, v___x_1891_);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg___boxed(lean_object* v_ext_1898_, lean_object* v_b_1899_, lean_object* v_kind_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
uint8_t v_kind_boxed_1904_; lean_object* v_res_1905_; 
v_kind_boxed_1904_ = lean_unbox(v_kind_1900_);
v_res_1905_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg(v_ext_1898_, v_b_1899_, v_kind_boxed_1904_, v___y_1901_, v___y_1902_);
lean_dec(v___y_1902_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0(lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_00_u03c3_1908_, lean_object* v_ext_1909_, lean_object* v_b_1910_, uint8_t v_kind_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; 
lean_inc_ref(v___y_1912_);
v___x_1915_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg(v_ext_1909_, v_b_1910_, v_kind_1911_, v___y_1912_, v___y_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_00_u03c3_1918_, lean_object* v_ext_1919_, lean_object* v_b_1920_, lean_object* v_kind_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
uint8_t v_kind_boxed_1925_; lean_object* v_res_1926_; 
v_kind_boxed_1925_ = lean_unbox(v_kind_1921_);
v_res_1926_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0(v_00_u03b1_1916_, v_00_u03b2_1917_, v_00_u03c3_1918_, v_ext_1919_, v_b_1920_, v_kind_boxed_1925_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1926_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__1(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocAttrCore___closed__0));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__3(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocAttrCore___closed__2));
v___x_1932_ = l_Lean_stringToMessageData(v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore(lean_object* v_ext_1933_, lean_object* v_declName_1934_, uint8_t v_kind_1935_, uint8_t v_post_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v_env_1941_; lean_object* v_options_1942_; lean_object* v_ref_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = lean_st_ref_get(v_a_1938_);
v_env_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1941_);
lean_dec(v___x_1940_);
v_options_1942_ = lean_ctor_get(v_a_1937_, 2);
v_ref_1943_ = lean_ctor_get(v_a_1937_, 5);
lean_inc_ref(v_options_1942_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_env_1941_);
lean_ctor_set(v___x_1944_, 1, v_options_1942_);
lean_inc(v_declName_1934_);
v___x_1945_ = l_Lean_Meta_Simp_getSimprocFromDeclImpl(v_declName_1934_, v___x_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1947_; lean_object* v_a_1948_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
lean_inc(v_declName_1934_);
v___x_1947_ = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(v_declName_1934_, v_a_1938_);
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1947_);
if (lean_obj_tag(v_a_1948_) == 1)
{
lean_object* v_val_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_val_1949_ = lean_ctor_get(v_a_1948_, 0);
lean_inc(v_val_1949_);
lean_dec_ref(v_a_1948_);
v___x_1950_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1950_, 0, v_declName_1934_);
lean_ctor_set(v___x_1950_, 1, v_val_1949_);
lean_ctor_set_uint8(v___x_1950_, sizeof(void*)*2, v_post_1936_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v_a_1946_);
lean_inc_ref(v_a_1937_);
v___x_1952_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Simp_addSimprocAttrCore_spec__0___redArg(v_ext_1933_, v___x_1951_, v_kind_1935_, v_a_1937_, v_a_1938_);
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; uint8_t v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_dec(v_a_1948_);
lean_dec(v_a_1946_);
lean_dec_ref(v_ext_1933_);
v___x_1953_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttrCore___closed__1, &l_Lean_Meta_Simp_addSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__1);
v___x_1954_ = 0;
v___x_1955_ = l_Lean_MessageData_ofConstName(v_declName_1934_, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1953_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttrCore___closed__3, &l_Lean_Meta_Simp_addSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__3);
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_1958_, v_a_1937_, v_a_1938_);
return v___x_1959_;
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_declName_1934_);
lean_dec_ref(v_ext_1933_);
v_a_1960_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1962_ = v___x_1945_;
v_isShared_1963_ = v_isSharedCheck_1971_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1945_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1971_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1964_ = lean_io_error_to_string(v_a_1960_);
v___x_1965_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
v___x_1966_ = l_Lean_MessageData_ofFormat(v___x_1965_);
lean_inc(v_ref_1943_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_ref_1943_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1967_);
v___x_1969_ = v___x_1962_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___boxed(lean_object* v_ext_1972_, lean_object* v_declName_1973_, lean_object* v_kind_1974_, lean_object* v_post_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
uint8_t v_kind_boxed_1979_; uint8_t v_post_boxed_1980_; lean_object* v_res_1981_; 
v_kind_boxed_1979_ = lean_unbox(v_kind_1974_);
v_post_boxed_1980_ = lean_unbox(v_post_1975_);
v_res_1981_ = l_Lean_Meta_Simp_addSimprocAttrCore(v_ext_1972_, v_declName_1973_, v_kind_boxed_1979_, v_post_boxed_1980_, v_a_1976_, v_a_1977_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
return v_res_1981_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3(lean_object* v_msg_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3___closed__0);
v___x_1985_ = lean_panic_fn(v___x_1984_, v_msg_1983_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v_ks_1990_; lean_object* v_vs_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2015_; 
v_ks_1990_ = lean_ctor_get(v_x_1986_, 0);
v_vs_1991_ = lean_ctor_get(v_x_1986_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_x_1986_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1993_ = v_x_1986_;
v_isShared_1994_ = v_isSharedCheck_2015_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_vs_1991_);
lean_inc(v_ks_1990_);
lean_dec(v_x_1986_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2015_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_array_get_size(v_ks_1990_);
v___x_1996_ = lean_nat_dec_lt(v_x_1987_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_x_1987_);
v___x_1997_ = lean_array_push(v_ks_1990_, v_x_1988_);
v___x_1998_ = lean_array_push(v_vs_1991_, v_x_1989_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_1998_);
lean_ctor_set(v___x_1993_, 0, v___x_1997_);
v___x_2000_ = v___x_1993_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
else
{
lean_object* v_k_x27_2002_; uint8_t v___x_2003_; 
v_k_x27_2002_ = lean_array_fget_borrowed(v_ks_1990_, v_x_1987_);
v___x_2003_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1988_, v_k_x27_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2005_; 
if (v_isShared_1994_ == 0)
{
v___x_2005_ = v___x_1993_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_ks_1990_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_vs_1991_);
v___x_2005_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_add(v_x_1987_, v___x_2006_);
lean_dec(v_x_1987_);
v_x_1986_ = v___x_2005_;
v_x_1987_ = v___x_2007_;
goto _start;
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
v___x_2010_ = lean_array_fset(v_ks_1990_, v_x_1987_, v_x_1988_);
v___x_2011_ = lean_array_fset(v_vs_1991_, v_x_1987_, v_x_1989_);
lean_dec(v_x_1987_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_2011_);
lean_ctor_set(v___x_1993_, 0, v___x_2010_);
v___x_2013_ = v___x_1993_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_n_2016_, lean_object* v_k_2017_, lean_object* v_v_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_n_2016_, v___x_2019_, v_k_2017_, v_v_2018_);
return v___x_2020_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(lean_object* v_x_2022_, size_t v_x_2023_, size_t v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v_es_2027_; size_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; lean_object* v_j_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_es_2027_ = lean_ctor_get(v_x_2022_, 0);
v___x_2028_ = ((size_t)5ULL);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_2031_ = lean_usize_land(v_x_2023_, v___x_2030_);
v_j_2032_ = lean_usize_to_nat(v___x_2031_);
v___x_2033_ = lean_array_get_size(v_es_2027_);
v___x_2034_ = lean_nat_dec_lt(v_j_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec(v_j_2032_);
lean_dec(v_x_2026_);
lean_dec(v_x_2025_);
return v_x_2022_;
}
else
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2071_; 
lean_inc_ref(v_es_2027_);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_x_2022_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v_x_2022_, 0);
lean_dec(v_unused_2072_);
v___x_2036_ = v_x_2022_;
v_isShared_2037_ = v_isSharedCheck_2071_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v_x_2022_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2071_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_v_2038_; lean_object* v___x_2039_; lean_object* v_xs_x27_2040_; lean_object* v___y_2042_; 
v_v_2038_ = lean_array_fget(v_es_2027_, v_j_2032_);
v___x_2039_ = lean_box(0);
v_xs_x27_2040_ = lean_array_fset(v_es_2027_, v_j_2032_, v___x_2039_);
switch(lean_obj_tag(v_v_2038_))
{
case 0:
{
lean_object* v_key_2047_; lean_object* v_val_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2058_; 
v_key_2047_ = lean_ctor_get(v_v_2038_, 0);
v_val_2048_ = lean_ctor_get(v_v_2038_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_v_2038_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2050_ = v_v_2038_;
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_val_2048_);
lean_inc(v_key_2047_);
lean_dec(v_v_2038_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2058_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2025_, v_key_2047_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_del_object(v___x_2050_);
v___x_2053_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2047_, v_val_2048_, v_x_2025_, v_x_2026_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
v___y_2042_ = v___x_2054_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2056_; 
lean_dec(v_val_2048_);
lean_dec(v_key_2047_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 1, v_x_2026_);
lean_ctor_set(v___x_2050_, 0, v_x_2025_);
v___x_2056_ = v___x_2050_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_x_2025_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_x_2026_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v___y_2042_ = v___x_2056_;
goto v___jp_2041_;
}
}
}
}
case 1:
{
lean_object* v_node_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2069_; 
v_node_2059_ = lean_ctor_get(v_v_2038_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_v_2038_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2061_ = v_v_2038_;
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_node_2059_);
lean_dec(v_v_2038_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2069_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2063_ = lean_usize_shift_right(v_x_2023_, v___x_2028_);
v___x_2064_ = lean_usize_add(v_x_2024_, v___x_2029_);
v___x_2065_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(v_node_2059_, v___x_2063_, v___x_2064_, v_x_2025_, v_x_2026_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2067_ = v___x_2061_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v___y_2042_ = v___x_2067_;
goto v___jp_2041_;
}
}
}
default: 
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_x_2025_);
lean_ctor_set(v___x_2070_, 1, v_x_2026_);
v___y_2042_ = v___x_2070_;
goto v___jp_2041_;
}
}
v___jp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_array_fset(v_xs_x27_2040_, v_j_2032_, v___y_2042_);
lean_dec(v_j_2032_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2043_);
v___x_2045_ = v___x_2036_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
else
{
lean_object* v_ks_2073_; lean_object* v_vs_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2094_; 
v_ks_2073_ = lean_ctor_get(v_x_2022_, 0);
v_vs_2074_ = lean_ctor_get(v_x_2022_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_2022_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2076_ = v_x_2022_;
v_isShared_2077_ = v_isSharedCheck_2094_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_vs_2074_);
lean_inc(v_ks_2073_);
lean_dec(v_x_2022_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2094_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_ks_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_vs_2074_);
v___x_2079_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v_newNode_2080_; uint8_t v___y_2082_; size_t v___x_2088_; uint8_t v___x_2089_; 
v_newNode_2080_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6___redArg(v___x_2079_, v_x_2025_, v_x_2026_);
v___x_2088_ = ((size_t)7ULL);
v___x_2089_ = lean_usize_dec_le(v___x_2088_, v_x_2024_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2090_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2080_);
v___x_2091_ = lean_unsigned_to_nat(4u);
v___x_2092_ = lean_nat_dec_lt(v___x_2090_, v___x_2091_);
lean_dec(v___x_2090_);
v___y_2082_ = v___x_2092_;
goto v___jp_2081_;
}
else
{
v___y_2082_ = v___x_2089_;
goto v___jp_2081_;
}
v___jp_2081_:
{
if (v___y_2082_ == 0)
{
lean_object* v_ks_2083_; lean_object* v_vs_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_ks_2083_ = lean_ctor_get(v_newNode_2080_, 0);
lean_inc_ref(v_ks_2083_);
v_vs_2084_ = lean_ctor_get(v_newNode_2080_, 1);
lean_inc_ref(v_vs_2084_);
lean_dec_ref(v_newNode_2080_);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_2087_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg(v_x_2024_, v_ks_2083_, v_vs_2084_, v___x_2085_, v___x_2086_);
lean_dec_ref(v_vs_2084_);
lean_dec_ref(v_ks_2083_);
return v___x_2087_;
}
else
{
return v_newNode_2080_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg(size_t v_depth_2095_, lean_object* v_keys_2096_, lean_object* v_vals_2097_, lean_object* v_i_2098_, lean_object* v_entries_2099_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_array_get_size(v_keys_2096_);
v___x_2101_ = lean_nat_dec_lt(v_i_2098_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec(v_i_2098_);
return v_entries_2099_;
}
else
{
lean_object* v_k_2102_; lean_object* v_v_2103_; uint64_t v___x_2104_; size_t v_h_2105_; size_t v___x_2106_; lean_object* v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; size_t v_h_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_k_2102_ = lean_array_fget_borrowed(v_keys_2096_, v_i_2098_);
v_v_2103_ = lean_array_fget_borrowed(v_vals_2097_, v_i_2098_);
v___x_2104_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_2102_);
v_h_2105_ = lean_uint64_to_usize(v___x_2104_);
v___x_2106_ = ((size_t)5ULL);
v___x_2107_ = lean_unsigned_to_nat(1u);
v___x_2108_ = ((size_t)1ULL);
v___x_2109_ = lean_usize_sub(v_depth_2095_, v___x_2108_);
v___x_2110_ = lean_usize_mul(v___x_2106_, v___x_2109_);
v_h_2111_ = lean_usize_shift_right(v_h_2105_, v___x_2110_);
v___x_2112_ = lean_nat_add(v_i_2098_, v___x_2107_);
lean_dec(v_i_2098_);
lean_inc(v_v_2103_);
lean_inc(v_k_2102_);
v___x_2113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(v_entries_2099_, v_h_2111_, v_depth_2095_, v_k_2102_, v_v_2103_);
v_i_2098_ = v___x_2112_;
v_entries_2099_ = v___x_2113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_2115_, lean_object* v_keys_2116_, lean_object* v_vals_2117_, lean_object* v_i_2118_, lean_object* v_entries_2119_){
_start:
{
size_t v_depth_boxed_2120_; lean_object* v_res_2121_; 
v_depth_boxed_2120_ = lean_unbox_usize(v_depth_2115_);
lean_dec(v_depth_2115_);
v_res_2121_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_boxed_2120_, v_keys_2116_, v_vals_2117_, v_i_2118_, v_entries_2119_);
lean_dec_ref(v_vals_2117_);
lean_dec_ref(v_keys_2116_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
size_t v_x_1681__boxed_2127_; size_t v_x_1682__boxed_2128_; lean_object* v_res_2129_; 
v_x_1681__boxed_2127_ = lean_unbox_usize(v_x_2123_);
lean_dec(v_x_2123_);
v_x_1682__boxed_2128_ = lean_unbox_usize(v_x_2124_);
lean_dec(v_x_2124_);
v_res_2129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(v_x_2122_, v_x_1681__boxed_2127_, v_x_1682__boxed_2128_, v_x_2125_, v_x_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1___redArg(lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
uint64_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2133_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2131_);
v___x_2134_ = lean_uint64_to_usize(v___x_2133_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(v_x_2130_, v___x_2134_, v___x_2135_, v_x_2131_, v_x_2132_);
return v___x_2136_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(lean_object* v_a_2137_, lean_object* v_b_2138_){
_start:
{
lean_object* v_fst_2139_; lean_object* v_fst_2140_; uint8_t v___x_2141_; 
v_fst_2139_ = lean_ctor_get(v_a_2137_, 0);
v_fst_2140_ = lean_ctor_get(v_b_2138_, 0);
v___x_2141_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_2139_, v_fst_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1___boxed(lean_object* v_a_2142_, lean_object* v_b_2143_){
_start:
{
uint8_t v_res_2144_; lean_object* v_r_2145_; 
v_res_2144_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v_a_2142_, v_b_2143_);
lean_dec_ref(v_b_2143_);
lean_dec_ref(v_a_2142_);
v_r_2145_ = lean_box(v_res_2144_);
return v_r_2145_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0(lean_object* v_x_2146_, lean_object* v_keys_2147_, lean_object* v_v_2148_, lean_object* v_k_2149_, lean_object* v_x_2150_){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v_c_2153_; lean_object* v___x_2154_; 
v___x_2151_ = lean_unsigned_to_nat(1u);
v___x_2152_ = lean_nat_add(v_x_2146_, v___x_2151_);
v_c_2153_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_2147_, v_v_2148_, v___x_2152_);
lean_dec(v___x_2152_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_k_2149_);
lean_ctor_set(v___x_2154_, 1, v_c_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0___boxed(lean_object* v_x_2155_, lean_object* v_keys_2156_, lean_object* v_v_2157_, lean_object* v_k_2158_, lean_object* v_x_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0(v_x_2155_, v_keys_2156_, v_v_2157_, v_k_2158_, v_x_2159_);
lean_dec_ref(v_keys_2156_);
lean_dec(v_x_2155_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__5_spec__10(lean_object* v_vs_2161_, lean_object* v_v_2162_, lean_object* v_i_2163_){
_start:
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_array_get_size(v_vs_2161_);
v___x_2165_ = lean_nat_dec_lt(v_i_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; 
lean_dec(v_i_2163_);
v___x_2166_ = lean_array_push(v_vs_2161_, v_v_2162_);
return v___x_2166_;
}
else
{
lean_object* v_toSimprocOLeanEntry_2167_; lean_object* v_declName_2168_; lean_object* v___x_2169_; lean_object* v_toSimprocOLeanEntry_2170_; lean_object* v_declName_2171_; uint8_t v___x_2172_; 
v_toSimprocOLeanEntry_2167_ = lean_ctor_get(v_v_2162_, 0);
v_declName_2168_ = lean_ctor_get(v_toSimprocOLeanEntry_2167_, 0);
v___x_2169_ = lean_array_fget_borrowed(v_vs_2161_, v_i_2163_);
v_toSimprocOLeanEntry_2170_ = lean_ctor_get(v___x_2169_, 0);
v_declName_2171_ = lean_ctor_get(v_toSimprocOLeanEntry_2170_, 0);
v___x_2172_ = lean_name_eq(v_declName_2168_, v_declName_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_unsigned_to_nat(1u);
v___x_2174_ = lean_nat_add(v_i_2163_, v___x_2173_);
lean_dec(v_i_2163_);
v_i_2163_ = v___x_2174_;
goto _start;
}
else
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_array_fset(v_vs_2161_, v_i_2163_, v_v_2162_);
lean_dec(v_i_2163_);
return v___x_2176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__5(lean_object* v_vs_2177_, lean_object* v_v_2178_){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__5_spec__10(v_vs_2177_, v_v_2178_, v___x_2179_);
return v___x_2180_;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__0));
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg(lean_object* v_x_2185_, lean_object* v_keys_2186_, lean_object* v_v_2187_, lean_object* v_k_2188_, lean_object* v_as_2189_, lean_object* v_k_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v_mid_2195_; lean_object* v_midVal_2196_; uint8_t v___x_2197_; 
v___x_2193_ = lean_nat_add(v_x_2191_, v_x_2192_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v_mid_2195_ = lean_nat_shiftr(v___x_2193_, v___x_2194_);
lean_dec(v___x_2193_);
v_midVal_2196_ = lean_array_fget(v_as_2189_, v_mid_2195_);
v___x_2197_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v_midVal_2196_, v_k_2190_);
if (v___x_2197_ == 0)
{
uint8_t v___x_2198_; 
lean_dec(v_x_2192_);
v___x_2198_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v_k_2190_, v_midVal_2196_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; uint8_t v___x_2200_; 
lean_dec(v_x_2191_);
v___x_2199_ = lean_array_get_size(v_as_2189_);
v___x_2200_ = lean_nat_dec_lt(v_mid_2195_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec(v_midVal_2196_);
lean_dec(v_mid_2195_);
lean_dec(v_k_2188_);
lean_dec_ref(v_v_2187_);
return v_as_2189_;
}
else
{
lean_object* v_snd_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2213_; 
v_snd_2201_ = lean_ctor_get(v_midVal_2196_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_midVal_2196_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v_midVal_2196_, 0);
lean_dec(v_unused_2214_);
v___x_2203_ = v_midVal_2196_;
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_snd_2201_);
lean_dec(v_midVal_2196_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2213_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v_xs_x27_2206_; lean_object* v___x_2207_; lean_object* v_c_2208_; lean_object* v___x_2210_; 
v___x_2205_ = lean_box(0);
v_xs_x27_2206_ = lean_array_fset(v_as_2189_, v_mid_2195_, v___x_2205_);
v___x_2207_ = lean_nat_add(v_x_2185_, v___x_2194_);
v_c_2208_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2(v_keys_2186_, v_v_2187_, v___x_2207_, v_snd_2201_);
lean_dec(v___x_2207_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v_c_2208_);
lean_ctor_set(v___x_2203_, 0, v_k_2188_);
v___x_2210_ = v___x_2203_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_k_2188_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v_c_2208_);
v___x_2210_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_array_fset(v_xs_x27_2206_, v_mid_2195_, v___x_2210_);
lean_dec(v_mid_2195_);
return v___x_2211_;
}
}
}
}
else
{
lean_dec(v_midVal_2196_);
v_x_2192_ = v_mid_2195_;
goto _start;
}
}
else
{
uint8_t v___x_2216_; 
lean_dec(v_midVal_2196_);
v___x_2216_ = lean_nat_dec_eq(v_mid_2195_, v_x_2191_);
if (v___x_2216_ == 0)
{
lean_dec(v_x_2191_);
v_x_2191_ = v_mid_2195_;
goto _start;
}
else
{
lean_object* v___x_2218_; lean_object* v_c_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_j_2222_; lean_object* v_as_2223_; lean_object* v___x_2224_; 
lean_dec(v_mid_2195_);
lean_dec(v_x_2192_);
v___x_2218_ = lean_nat_add(v_x_2185_, v___x_2194_);
v_c_2219_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_2186_, v_v_2187_, v___x_2218_);
lean_dec(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v_k_2188_);
lean_ctor_set(v___x_2220_, 1, v_c_2219_);
v___x_2221_ = lean_nat_add(v_x_2191_, v___x_2194_);
lean_dec(v_x_2191_);
v_j_2222_ = lean_array_get_size(v_as_2189_);
v_as_2223_ = lean_array_push(v_as_2189_, v___x_2220_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2221_, v_as_2223_, v_j_2222_);
lean_dec(v___x_2221_);
return v___x_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6(lean_object* v_x_2225_, lean_object* v_keys_2226_, lean_object* v_v_2227_, lean_object* v_k_2228_, lean_object* v_as_2229_, lean_object* v_k_2230_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2231_ = lean_array_get_size(v_as_2229_);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_nat_dec_eq(v___x_2231_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2234_ = lean_array_fget_borrowed(v_as_2229_, v___x_2232_);
v___x_2235_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v_k_2230_, v___x_2234_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
v___x_2236_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v___x_2234_, v_k_2230_);
if (v___x_2236_ == 0)
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_nat_dec_lt(v___x_2232_, v___x_2231_);
if (v___x_2237_ == 0)
{
lean_dec(v_k_2228_);
lean_dec_ref(v_v_2227_);
return v_as_2229_;
}
else
{
lean_object* v___x_2238_; lean_object* v_xs_x27_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_inc(v___x_2234_);
v___x_2238_ = lean_box(0);
v_xs_x27_2239_ = lean_array_fset(v_as_2229_, v___x_2232_, v___x_2238_);
v___x_2240_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2(v_x_2225_, v_keys_2226_, v_v_2227_, v_k_2228_, v___x_2234_);
v___x_2241_ = lean_array_fset(v_xs_x27_2239_, v___x_2232_, v___x_2240_);
return v___x_2241_;
}
}
else
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_sub(v___x_2231_, v___x_2242_);
v___x_2244_ = lean_array_fget_borrowed(v_as_2229_, v___x_2243_);
v___x_2245_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v___x_2244_, v_k_2230_);
if (v___x_2245_ == 0)
{
uint8_t v___x_2246_; 
v___x_2246_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__1(v_k_2230_, v___x_2244_);
if (v___x_2246_ == 0)
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_nat_dec_lt(v___x_2243_, v___x_2231_);
if (v___x_2247_ == 0)
{
lean_dec(v___x_2243_);
lean_dec(v_k_2228_);
lean_dec_ref(v_v_2227_);
return v_as_2229_;
}
else
{
lean_object* v___x_2248_; lean_object* v_xs_x27_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc(v___x_2244_);
v___x_2248_ = lean_box(0);
v_xs_x27_2249_ = lean_array_fset(v_as_2229_, v___x_2243_, v___x_2248_);
v___x_2250_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2(v_x_2225_, v_keys_2226_, v_v_2227_, v_k_2228_, v___x_2244_);
v___x_2251_ = lean_array_fset(v_xs_x27_2249_, v___x_2243_, v___x_2250_);
lean_dec(v___x_2243_);
return v___x_2251_;
}
}
else
{
lean_object* v___x_2252_; 
v___x_2252_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg(v_x_2225_, v_keys_2226_, v_v_2227_, v_k_2228_, v_as_2229_, v_k_2230_, v___x_2232_, v___x_2243_);
return v___x_2252_;
}
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec(v___x_2243_);
v___x_2253_ = lean_box(0);
v___x_2254_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0(v_x_2225_, v_keys_2226_, v_v_2227_, v_k_2228_, v___x_2253_);
v___x_2255_ = lean_array_push(v_as_2229_, v___x_2254_);
return v___x_2255_;
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_as_2258_; lean_object* v___x_2259_; 
v___x_2256_ = lean_box(0);
v___x_2257_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0(v_x_2225_, v_keys_2226_, v_v_2227_, v_k_2228_, v___x_2256_);
v_as_2258_ = lean_array_push(v_as_2229_, v___x_2257_);
v___x_2259_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_2232_, v_as_2258_, v___x_2231_);
return v___x_2259_;
}
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_box(0);
v___x_2261_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__0(v_x_2225_, v_keys_2226_, v_v_2227_, v_k_2228_, v___x_2260_);
v___x_2262_ = lean_array_push(v_as_2229_, v___x_2261_);
return v___x_2262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2(lean_object* v_keys_2263_, lean_object* v_v_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v_vs_2267_; lean_object* v_children_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2285_; 
v_vs_2267_ = lean_ctor_get(v_x_2266_, 0);
v_children_2268_ = lean_ctor_get(v_x_2266_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_x_2266_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2270_ = v_x_2266_;
v_isShared_2271_ = v_isSharedCheck_2285_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_children_2268_);
lean_inc(v_vs_2267_);
lean_dec(v_x_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2285_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = lean_array_get_size(v_keys_2263_);
v___x_2273_ = lean_nat_dec_lt(v_x_2265_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__5(v_vs_2267_, v_v_2264_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2274_);
v___x_2276_ = v___x_2270_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_children_2268_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
else
{
lean_object* v_k_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v_c_2281_; lean_object* v___x_2283_; 
v_k_2278_ = lean_array_fget_borrowed(v_keys_2263_, v_x_2265_);
v___x_2279_ = lean_obj_once(&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__1, &l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__1_once, _init_l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___closed__1);
lean_inc(v_k_2278_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v_k_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
lean_inc(v_k_2278_);
v_c_2281_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6(v_x_2265_, v_keys_2263_, v_v_2264_, v_k_2278_, v_children_2268_, v___x_2280_);
lean_dec_ref(v___x_2280_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v_c_2281_);
v___x_2283_ = v___x_2270_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_vs_2267_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_c_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2(lean_object* v_x_2286_, lean_object* v_keys_2287_, lean_object* v_v_2288_, lean_object* v_k_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v_snd_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2301_; 
v_snd_2291_ = lean_ctor_get(v_x_2290_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_x_2290_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v_x_2290_, 0);
lean_dec(v_unused_2302_);
v___x_2293_ = v_x_2290_;
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_snd_2291_);
lean_dec(v_x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2301_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v_c_2297_; lean_object* v___x_2299_; 
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_nat_add(v_x_2286_, v___x_2295_);
v_c_2297_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2(v_keys_2287_, v_v_2288_, v___x_2296_, v_snd_2291_);
lean_dec(v___x_2296_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v_c_2297_);
lean_ctor_set(v___x_2293_, 0, v_k_2289_);
v___x_2299_ = v___x_2293_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_k_2289_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_c_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2___boxed(lean_object* v_x_2303_, lean_object* v_keys_2304_, lean_object* v_v_2305_, lean_object* v_k_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___lam__2(v_x_2303_, v_keys_2304_, v_v_2305_, v_k_2306_, v_x_2307_);
lean_dec_ref(v_keys_2304_);
lean_dec(v_x_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2___boxed(lean_object* v_keys_2309_, lean_object* v_v_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2(v_keys_2309_, v_v_2310_, v_x_2311_, v_x_2312_);
lean_dec(v_x_2311_);
lean_dec_ref(v_keys_2309_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg___boxed(lean_object* v_x_2314_, lean_object* v_keys_2315_, lean_object* v_v_2316_, lean_object* v_k_2317_, lean_object* v_as_2318_, lean_object* v_k_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg(v_x_2314_, v_keys_2315_, v_v_2316_, v_k_2317_, v_as_2318_, v_k_2319_, v_x_2320_, v_x_2321_);
lean_dec_ref(v_k_2319_);
lean_dec_ref(v_keys_2315_);
lean_dec(v_x_2314_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6___boxed(lean_object* v_x_2323_, lean_object* v_keys_2324_, lean_object* v_v_2325_, lean_object* v_k_2326_, lean_object* v_as_2327_, lean_object* v_k_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6(v_x_2323_, v_keys_2324_, v_v_2325_, v_k_2326_, v_as_2327_, v_k_2328_);
lean_dec_ref(v_k_2328_);
lean_dec_ref(v_keys_2324_);
lean_dec(v_x_2323_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_keys_2330_, lean_object* v_vals_2331_, lean_object* v_i_2332_, lean_object* v_k_2333_){
_start:
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2334_ = lean_array_get_size(v_keys_2330_);
v___x_2335_ = lean_nat_dec_lt(v_i_2332_, v___x_2334_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_dec(v_i_2332_);
v___x_2336_ = lean_box(0);
return v___x_2336_;
}
else
{
lean_object* v_k_x27_2337_; uint8_t v___x_2338_; 
v_k_x27_2337_ = lean_array_fget_borrowed(v_keys_2330_, v_i_2332_);
v___x_2338_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_2333_, v_k_x27_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_nat_add(v_i_2332_, v___x_2339_);
lean_dec(v_i_2332_);
v_i_2332_ = v___x_2340_;
goto _start;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_array_fget_borrowed(v_vals_2331_, v_i_2332_);
lean_dec(v_i_2332_);
lean_inc(v___x_2342_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_keys_2344_, lean_object* v_vals_2345_, lean_object* v_i_2346_, lean_object* v_k_2347_){
_start:
{
lean_object* v_res_2348_; 
v_res_2348_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2344_, v_vals_2345_, v_i_2346_, v_k_2347_);
lean_dec(v_k_2347_);
lean_dec_ref(v_vals_2345_);
lean_dec_ref(v_keys_2344_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg(lean_object* v_x_2349_, size_t v_x_2350_, lean_object* v_x_2351_){
_start:
{
if (lean_obj_tag(v_x_2349_) == 0)
{
lean_object* v_es_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2373_; 
v_es_2352_ = lean_ctor_get(v_x_2349_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2349_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2354_ = v_x_2349_;
v_isShared_2355_ = v_isSharedCheck_2373_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_es_2352_);
lean_dec(v_x_2349_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2373_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; size_t v___x_2357_; size_t v___x_2358_; size_t v___x_2359_; lean_object* v_j_2360_; lean_object* v___x_2361_; 
v___x_2356_ = lean_box(2);
v___x_2357_ = ((size_t)5ULL);
v___x_2358_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
v___x_2359_ = lean_usize_land(v_x_2350_, v___x_2358_);
v_j_2360_ = lean_usize_to_nat(v___x_2359_);
v___x_2361_ = lean_array_get(v___x_2356_, v_es_2352_, v_j_2360_);
lean_dec(v_j_2360_);
lean_dec_ref(v_es_2352_);
switch(lean_obj_tag(v___x_2361_))
{
case 0:
{
lean_object* v_key_2362_; lean_object* v_val_2363_; uint8_t v___x_2364_; 
v_key_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_key_2362_);
v_val_2363_ = lean_ctor_get(v___x_2361_, 1);
lean_inc(v_val_2363_);
lean_dec_ref(v___x_2361_);
v___x_2364_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_2351_, v_key_2362_);
lean_dec(v_key_2362_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec(v_val_2363_);
lean_del_object(v___x_2354_);
v___x_2365_ = lean_box(0);
return v___x_2365_;
}
else
{
lean_object* v___x_2367_; 
if (v_isShared_2355_ == 0)
{
lean_ctor_set_tag(v___x_2354_, 1);
lean_ctor_set(v___x_2354_, 0, v_val_2363_);
v___x_2367_ = v___x_2354_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_val_2363_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
case 1:
{
lean_object* v_node_2369_; size_t v___x_2370_; 
lean_del_object(v___x_2354_);
v_node_2369_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_node_2369_);
lean_dec_ref(v___x_2361_);
v___x_2370_ = lean_usize_shift_right(v_x_2350_, v___x_2357_);
v_x_2349_ = v_node_2369_;
v_x_2350_ = v___x_2370_;
goto _start;
}
default: 
{
lean_object* v___x_2372_; 
lean_del_object(v___x_2354_);
v___x_2372_ = lean_box(0);
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_ks_2374_; lean_object* v_vs_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_ks_2374_ = lean_ctor_get(v_x_2349_, 0);
lean_inc_ref(v_ks_2374_);
v_vs_2375_ = lean_ctor_get(v_x_2349_, 1);
lean_inc_ref(v_vs_2375_);
lean_dec_ref(v_x_2349_);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_2374_, v_vs_2375_, v___x_2376_, v_x_2351_);
lean_dec_ref(v_vs_2375_);
lean_dec_ref(v_ks_2374_);
return v___x_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2378_, lean_object* v_x_2379_, lean_object* v_x_2380_){
_start:
{
size_t v_x_2115__boxed_2381_; lean_object* v_res_2382_; 
v_x_2115__boxed_2381_ = lean_unbox_usize(v_x_2379_);
lean_dec(v_x_2379_);
v_res_2382_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg(v_x_2378_, v_x_2115__boxed_2381_, v_x_2380_);
lean_dec(v_x_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg(lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
uint64_t v___x_2385_; size_t v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_2384_);
v___x_2386_ = lean_uint64_to_usize(v___x_2385_);
v___x_2387_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg(v_x_2383_, v___x_2386_, v_x_2384_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg___boxed(lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg(v_x_2388_, v_x_2389_);
lean_dec(v_x_2389_);
return v_res_2390_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2394_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__2));
v___x_2395_ = lean_unsigned_to_nat(23u);
v___x_2396_ = lean_unsigned_to_nat(166u);
v___x_2397_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__1));
v___x_2398_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__0));
v___x_2399_ = l_mkPanicMessageWithDecl(v___x_2398_, v___x_2397_, v___x_2396_, v___x_2395_, v___x_2394_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0(lean_object* v_d_2400_, lean_object* v_keys_2401_, lean_object* v_v_2402_){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; uint8_t v___x_2405_; 
v___x_2403_ = lean_array_get_size(v_keys_2401_);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_nat_dec_eq(v___x_2403_, v___x_2404_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v_k_2407_; lean_object* v___x_2408_; 
v___x_2406_ = lean_box(0);
v_k_2407_ = lean_array_get_borrowed(v___x_2406_, v_keys_2401_, v___x_2404_);
lean_inc_ref(v_d_2400_);
v___x_2408_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg(v_d_2400_, v_k_2407_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v___x_2409_; lean_object* v_c_2410_; lean_object* v___x_2411_; 
v___x_2409_ = lean_unsigned_to_nat(1u);
v_c_2410_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_2401_, v_v_2402_, v___x_2409_);
lean_inc(v_k_2407_);
v___x_2411_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1___redArg(v_d_2400_, v_k_2407_, v_c_2410_);
return v___x_2411_;
}
else
{
lean_object* v_val_2412_; lean_object* v___x_2413_; lean_object* v_c_2414_; lean_object* v___x_2415_; 
v_val_2412_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_val_2412_);
lean_dec_ref(v___x_2408_);
v___x_2413_ = lean_unsigned_to_nat(1u);
v_c_2414_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2(v_keys_2401_, v_v_2402_, v___x_2413_, v_val_2412_);
lean_inc(v_k_2407_);
v___x_2415_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1___redArg(v_d_2400_, v_k_2407_, v_c_2414_);
return v___x_2415_;
}
}
else
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
lean_dec_ref(v_v_2402_);
lean_dec_ref(v_d_2400_);
v___x_2416_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___closed__3);
v___x_2417_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__3(v___x_2416_);
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0___boxed(lean_object* v_d_2418_, lean_object* v_keys_2419_, lean_object* v_v_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0(v_d_2418_, v_keys_2419_, v_v_2420_);
lean_dec_ref(v_keys_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object* v_s_2422_, lean_object* v_keys_2423_, lean_object* v_declName_2424_, uint8_t v_post_2425_, lean_object* v_proc_2426_){
_start:
{
lean_object* v_pre_2427_; lean_object* v_post_2428_; lean_object* v_simprocNames_2429_; lean_object* v_erased_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2449_; 
v_pre_2427_ = lean_ctor_get(v_s_2422_, 0);
v_post_2428_ = lean_ctor_get(v_s_2422_, 1);
v_simprocNames_2429_ = lean_ctor_get(v_s_2422_, 2);
v_erased_2430_ = lean_ctor_get(v_s_2422_, 3);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_s_2422_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2432_ = v_s_2422_;
v_isShared_2433_ = v_isSharedCheck_2449_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_erased_2430_);
lean_inc(v_simprocNames_2429_);
lean_inc(v_post_2428_);
lean_inc(v_pre_2427_);
lean_dec(v_s_2422_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2449_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_box(0);
lean_inc(v_declName_2424_);
v___x_2435_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0___redArg(v_simprocNames_2429_, v_declName_2424_, v___x_2434_);
v___x_2436_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Simp_Simprocs_erase_spec__0___redArg(v_erased_2430_, v_declName_2424_);
if (v_post_2425_ == 0)
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc_ref(v_keys_2423_);
v___x_2437_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2437_, 0, v_declName_2424_);
lean_ctor_set(v___x_2437_, 1, v_keys_2423_);
lean_ctor_set_uint8(v___x_2437_, sizeof(void*)*2, v_post_2425_);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v_proc_2426_);
v___x_2439_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0(v_pre_2427_, v_keys_2423_, v___x_2438_);
lean_dec_ref(v_keys_2423_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 3, v___x_2436_);
lean_ctor_set(v___x_2432_, 2, v___x_2435_);
lean_ctor_set(v___x_2432_, 0, v___x_2439_);
v___x_2441_ = v___x_2432_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_post_2428_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2442_, 3, v___x_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_inc_ref(v_keys_2423_);
v___x_2443_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2443_, 0, v_declName_2424_);
lean_ctor_set(v___x_2443_, 1, v_keys_2423_);
lean_ctor_set_uint8(v___x_2443_, sizeof(void*)*2, v_post_2425_);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_proc_2426_);
v___x_2445_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0(v_post_2428_, v_keys_2423_, v___x_2444_);
lean_dec_ref(v_keys_2423_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 3, v___x_2436_);
lean_ctor_set(v___x_2432_, 2, v___x_2435_);
lean_ctor_set(v___x_2432_, 1, v___x_2445_);
v___x_2447_ = v___x_2432_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_pre_2427_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v___x_2436_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore___boxed(lean_object* v_s_2450_, lean_object* v_keys_2451_, lean_object* v_declName_2452_, lean_object* v_post_2453_, lean_object* v_proc_2454_){
_start:
{
uint8_t v_post_boxed_2455_; lean_object* v_res_2456_; 
v_post_boxed_2455_ = lean_unbox(v_post_2453_);
v_res_2456_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2450_, v_keys_2451_, v_declName_2452_, v_post_boxed_2455_, v_proc_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(lean_object* v_00_u03b2_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___redArg(v_x_2458_, v_x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(v_00_u03b2_2461_, v_x_2462_, v_x_2463_);
lean_dec(v_x_2463_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1(lean_object* v_00_u03b2_2465_, lean_object* v_x_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1___redArg(v_x_2466_, v_x_2467_, v_x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2470_, lean_object* v_x_2471_, size_t v_x_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___redArg(v_x_2471_, v_x_2472_, v_x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2475_, lean_object* v_x_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
size_t v_x_2293__boxed_2479_; lean_object* v_res_2480_; 
v_x_2293__boxed_2479_ = lean_unbox_usize(v_x_2477_);
lean_dec(v_x_2477_);
v_res_2480_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1(v_00_u03b2_2475_, v_x_2476_, v_x_2293__boxed_2479_, v_x_2478_);
lean_dec(v_x_2478_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2481_, lean_object* v_x_2482_, size_t v_x_2483_, size_t v_x_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___redArg(v_x_2482_, v_x_2483_, v_x_2484_, v_x_2485_, v_x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2488_, lean_object* v_x_2489_, lean_object* v_x_2490_, lean_object* v_x_2491_, lean_object* v_x_2492_, lean_object* v_x_2493_){
_start:
{
size_t v_x_2304__boxed_2494_; size_t v_x_2305__boxed_2495_; lean_object* v_res_2496_; 
v_x_2304__boxed_2494_ = lean_unbox_usize(v_x_2490_);
lean_dec(v_x_2490_);
v_x_2305__boxed_2495_ = lean_unbox_usize(v_x_2491_);
lean_dec(v_x_2491_);
v_res_2496_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3(v_00_u03b2_2488_, v_x_2489_, v_x_2304__boxed_2494_, v_x_2305__boxed_2495_, v_x_2492_, v_x_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2497_, lean_object* v_keys_2498_, lean_object* v_vals_2499_, lean_object* v_heq_2500_, lean_object* v_i_2501_, lean_object* v_k_2502_){
_start:
{
lean_object* v___x_2503_; 
v___x_2503_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_2498_, v_vals_2499_, v_i_2501_, v_k_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_2504_, lean_object* v_keys_2505_, lean_object* v_vals_2506_, lean_object* v_heq_2507_, lean_object* v_i_2508_, lean_object* v_k_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2504_, v_keys_2505_, v_vals_2506_, v_heq_2507_, v_i_2508_, v_k_2509_);
lean_dec(v_k_2509_);
lean_dec_ref(v_vals_2506_);
lean_dec_ref(v_keys_2505_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_2511_, lean_object* v_n_2512_, lean_object* v_k_2513_, lean_object* v_v_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6___redArg(v_n_2512_, v_k_2513_, v_v_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_2516_, size_t v_depth_2517_, lean_object* v_keys_2518_, lean_object* v_vals_2519_, lean_object* v_heq_2520_, lean_object* v_i_2521_, lean_object* v_entries_2522_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___redArg(v_depth_2517_, v_keys_2518_, v_vals_2519_, v_i_2521_, v_entries_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_2524_, lean_object* v_depth_2525_, lean_object* v_keys_2526_, lean_object* v_vals_2527_, lean_object* v_heq_2528_, lean_object* v_i_2529_, lean_object* v_entries_2530_){
_start:
{
size_t v_depth_boxed_2531_; lean_object* v_res_2532_; 
v_depth_boxed_2531_ = lean_unbox_usize(v_depth_2525_);
lean_dec(v_depth_2525_);
v_res_2532_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2524_, v_depth_boxed_2531_, v_keys_2526_, v_vals_2527_, v_heq_2528_, v_i_2529_, v_entries_2530_);
lean_dec_ref(v_vals_2527_);
lean_dec_ref(v_keys_2526_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12(lean_object* v_x_2533_, lean_object* v_keys_2534_, lean_object* v_v_2535_, lean_object* v_k_2536_, lean_object* v_as_2537_, lean_object* v_k_2538_, lean_object* v_x_2539_, lean_object* v_x_2540_, lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___redArg(v_x_2533_, v_keys_2534_, v_v_2535_, v_k_2536_, v_as_2537_, v_k_2538_, v_x_2539_, v_x_2540_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12___boxed(lean_object* v_x_2544_, lean_object* v_keys_2545_, lean_object* v_v_2546_, lean_object* v_k_2547_, lean_object* v_as_2548_, lean_object* v_k_2549_, lean_object* v_x_2550_, lean_object* v_x_2551_, lean_object* v_x_2552_, lean_object* v_x_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__2_spec__6_spec__12(v_x_2544_, v_keys_2545_, v_v_2546_, v_k_2547_, v_as_2548_, v_k_2549_, v_x_2550_, v_x_2551_, v_x_2552_, v_x_2553_);
lean_dec_ref(v_k_2549_);
lean_dec_ref(v_keys_2545_);
lean_dec(v_x_2544_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2555_, lean_object* v_x_2556_, lean_object* v_x_2557_, lean_object* v_x_2558_, lean_object* v_x_2559_){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__1_spec__3_spec__6_spec__8___redArg(v_x_2556_, v_x_2557_, v_x_2558_, v_x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object* v_ref_2563_, lean_object* v_declName_2564_, uint8_t v_post_2565_, lean_object* v_proc_2566_){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_keys_2570_; lean_object* v___x_2571_; 
v___x_2568_ = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
v___x_2569_ = lean_st_ref_get(v___x_2568_);
v_keys_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_keys_2570_);
lean_dec(v___x_2569_);
v___x_2571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v_keys_2570_, v_declName_2564_);
lean_dec_ref(v_keys_2570_);
if (lean_obj_tag(v___x_2571_) == 1)
{
lean_object* v_val_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2582_; 
v_val_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2582_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_val_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2582_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2576_ = lean_st_ref_take(v_ref_2563_);
v___x_2577_ = l_Lean_Meta_Simp_Simprocs_addCore(v___x_2576_, v_val_2572_, v_declName_2564_, v_post_2565_, v_proc_2566_);
v___x_2578_ = lean_st_ref_set(v_ref_2563_, v___x_2577_);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2578_);
v___x_2580_ = v___x_2574_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec(v___x_2571_);
lean_dec_ref(v_proc_2566_);
v___x_2583_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__0));
v___x_2584_ = l_Lean_privateToUserName(v_declName_2564_);
v___x_2585_ = 1;
v___x_2586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2584_, v___x_2585_);
v___x_2587_ = lean_string_append(v___x_2583_, v___x_2586_);
lean_dec_ref(v___x_2586_);
v___x_2588_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___closed__1));
v___x_2589_ = lean_string_append(v___x_2587_, v___x_2588_);
v___x_2590_ = lean_mk_io_user_error(v___x_2589_);
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___boxed(lean_object* v_ref_2592_, lean_object* v_declName_2593_, lean_object* v_post_2594_, lean_object* v_proc_2595_, lean_object* v_a_2596_){
_start:
{
uint8_t v_post_boxed_2597_; lean_object* v_res_2598_; 
v_post_boxed_2597_ = lean_unbox(v_post_2594_);
v_res_2598_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v_ref_2592_, v_declName_2593_, v_post_boxed_2597_, v_proc_2595_);
lean_dec(v_ref_2592_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object* v_declName_2599_, uint8_t v_post_2600_, lean_object* v_proc_2601_){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = l_Lean_Meta_Simp_builtinSimprocsRef;
v___x_2604_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v___x_2603_, v_declName_2599_, v_post_2600_, v_proc_2601_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___boxed(lean_object* v_declName_2605_, lean_object* v_post_2606_, lean_object* v_proc_2607_, lean_object* v_a_2608_){
_start:
{
uint8_t v_post_boxed_2609_; lean_object* v_res_2610_; 
v_post_boxed_2609_ = lean_unbox(v_post_2606_);
v_res_2610_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v_declName_2605_, v_post_boxed_2609_, v_proc_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object* v_declName_2611_, uint8_t v_post_2612_, lean_object* v_proc_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = l_Lean_Meta_Simp_builtinSEvalprocsRef;
v___x_2616_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v___x_2615_, v_declName_2611_, v_post_2612_, v_proc_2613_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___boxed(lean_object* v_declName_2617_, lean_object* v_post_2618_, lean_object* v_proc_2619_, lean_object* v_a_2620_){
_start:
{
uint8_t v_post_boxed_2621_; lean_object* v_res_2622_; 
v_post_boxed_2621_ = lean_unbox(v_post_2618_);
v_res_2622_ = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(v_declName_2617_, v_post_boxed_2621_, v_proc_2619_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object* v_s_2623_, lean_object* v_declName_2624_, uint8_t v_post_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_a_2630_; lean_object* v___x_2649_; lean_object* v_env_2650_; lean_object* v_options_2651_; lean_object* v_ref_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2649_ = lean_st_ref_get(v_a_2627_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v_options_2651_ = lean_ctor_get(v_a_2626_, 2);
v_ref_2652_ = lean_ctor_get(v_a_2626_, 5);
lean_inc_ref(v_options_2651_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_env_2650_);
lean_ctor_set(v___x_2653_, 1, v_options_2651_);
lean_inc(v_declName_2624_);
v___x_2654_ = l_Lean_Meta_Simp_getSimprocFromDeclImpl(v_declName_2624_, v___x_2653_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2654_);
v_a_2630_ = v_a_2655_;
goto v___jp_2629_;
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2707_; 
v_a_2656_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2658_ = v___x_2654_;
v_isShared_2659_ = v_isSharedCheck_2707_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2707_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___y_2665_; uint8_t v___x_2705_; 
v___x_2660_ = lean_io_error_to_string(v_a_2656_);
v___x_2661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
v___x_2662_ = l_Lean_MessageData_ofFormat(v___x_2661_);
lean_inc(v_ref_2652_);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_ref_2652_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2705_ = l_Lean_Exception_isInterrupt(v___x_2663_);
if (v___x_2705_ == 0)
{
uint8_t v___x_2706_; 
lean_inc_ref(v___x_2663_);
v___x_2706_ = l_Lean_Exception_isRuntime(v___x_2663_);
v___y_2665_ = v___x_2706_;
goto v___jp_2664_;
}
else
{
v___y_2665_ = v___x_2705_;
goto v___jp_2664_;
}
v___jp_2664_:
{
if (v___y_2665_ == 0)
{
lean_object* v___x_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2701_; 
lean_del_object(v___x_2658_);
v___x_2666_ = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(v_declName_2624_, v_a_2627_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2701_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2701_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_unbox(v_a_2667_);
lean_dec(v_a_2667_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2673_; 
lean_dec(v_declName_2624_);
lean_dec_ref(v_s_2623_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 0, v___x_2663_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2663_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_procs_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2699_; 
lean_del_object(v___x_2669_);
lean_dec_ref(v___x_2663_);
v___x_2675_ = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
v___x_2676_ = lean_st_ref_get(v___x_2675_);
v_procs_2677_ = lean_ctor_get(v___x_2676_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2699_ == 0)
{
lean_object* v_unused_2700_; 
v_unused_2700_ = lean_ctor_get(v___x_2676_, 0);
lean_dec(v_unused_2700_);
v___x_2679_ = v___x_2676_;
v_isShared_2680_ = v_isSharedCheck_2699_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_procs_2677_);
lean_dec(v___x_2676_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2699_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v_procs_2677_, v_declName_2624_);
lean_dec_ref(v_procs_2677_);
if (lean_obj_tag(v___x_2681_) == 1)
{
lean_object* v_val_2682_; 
lean_del_object(v___x_2679_);
v_val_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_val_2682_);
lean_dec_ref(v___x_2681_);
v_a_2630_ = v_val_2682_;
goto v___jp_2629_;
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec(v___x_2681_);
lean_dec_ref(v_s_2623_);
v___x_2683_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttrCore___closed__1, &l_Lean_Meta_Simp_addSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__1);
v___x_2684_ = l_Lean_MessageData_ofConstName(v_declName_2624_, v___y_2665_);
if (v_isShared_2680_ == 0)
{
lean_ctor_set_tag(v___x_2679_, 7);
lean_ctor_set(v___x_2679_, 1, v___x_2684_);
lean_ctor_set(v___x_2679_, 0, v___x_2683_);
v___x_2686_ = v___x_2679_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
v___x_2687_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttrCore___closed__3, &l_Lean_Meta_Simp_addSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__3);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_2688_, v_a_2626_, v_a_2627_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
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
lean_object* v___x_2703_; 
lean_dec(v_declName_2624_);
lean_dec_ref(v_s_2623_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2663_);
v___x_2703_ = v___x_2658_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2663_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
v___jp_2629_:
{
lean_object* v___x_2631_; lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2648_; 
lean_inc(v_declName_2624_);
v___x_2631_ = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(v_declName_2624_, v_a_2627_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2634_ = v___x_2631_;
v_isShared_2635_ = v_isSharedCheck_2648_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2648_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
if (lean_obj_tag(v_a_2632_) == 1)
{
lean_object* v_val_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
v_val_2636_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_val_2636_);
lean_dec_ref(v_a_2632_);
v___x_2637_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_2623_, v_val_2636_, v_declName_2624_, v_post_2625_, v_a_2630_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2637_);
v___x_2639_ = v___x_2634_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
else
{
lean_object* v___x_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_del_object(v___x_2634_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2630_);
lean_dec_ref(v_s_2623_);
v___x_2641_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttrCore___closed__1, &l_Lean_Meta_Simp_addSimprocAttrCore___closed__1_once, _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__1);
v___x_2642_ = 0;
v___x_2643_ = l_Lean_MessageData_ofConstName(v_declName_2624_, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2641_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttrCore___closed__3, &l_Lean_Meta_Simp_addSimprocAttrCore___closed__3_once, _init_l_Lean_Meta_Simp_addSimprocAttrCore___closed__3);
v___x_2646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2644_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
v___x_2647_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_2646_, v_a_2626_, v_a_2627_);
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___boxed(lean_object* v_s_2708_, lean_object* v_declName_2709_, lean_object* v_post_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
uint8_t v_post_boxed_2714_; lean_object* v_res_2715_; 
v_post_boxed_2714_ = lean_unbox(v_post_2710_);
v_res_2715_ = l_Lean_Meta_Simp_Simprocs_add(v_s_2708_, v_declName_2709_, v_post_boxed_2714_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(lean_object* v_upperBound_2716_, lean_object* v_a_2717_, lean_object* v_b_2718_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_nat_dec_lt(v_a_2717_, v_upperBound_2716_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; 
lean_dec(v_a_2717_);
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_b_2718_);
return v___x_2721_;
}
else
{
lean_object* v_fst_2722_; lean_object* v_snd_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2736_; 
v_fst_2722_ = lean_ctor_get(v_b_2718_, 0);
v_snd_2723_ = lean_ctor_get(v_b_2718_, 1);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_b_2718_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2725_ = v_b_2718_;
v_isShared_2726_ = v_isSharedCheck_2736_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snd_2723_);
lean_inc(v_fst_2722_);
lean_dec(v_b_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2736_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2727_ = l_Lean_Expr_appArg_x21(v_snd_2723_);
v___x_2728_ = lean_array_push(v_fst_2722_, v___x_2727_);
v___x_2729_ = l_Lean_Expr_appFn_x21(v_snd_2723_);
lean_dec(v_snd_2723_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2729_);
lean_ctor_set(v___x_2725_, 0, v___x_2728_);
v___x_2731_ = v___x_2725_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_unsigned_to_nat(1u);
v___x_2733_ = lean_nat_add(v_a_2717_, v___x_2732_);
lean_dec(v_a_2717_);
v_a_2717_ = v___x_2733_;
v_b_2718_ = v___x_2731_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg___boxed(lean_object* v_upperBound_2737_, lean_object* v_a_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(v_upperBound_2737_, v_a_2738_, v_b_2739_);
lean_dec(v_upperBound_2737_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try(lean_object* v_s_2744_, lean_object* v_numExtraArgs_2745_, lean_object* v_e_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v___x_2755_; lean_object* v_extraArgs_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = lean_unsigned_to_nat(0u);
v_extraArgs_2756_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_try___closed__0));
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_extraArgs_2756_);
lean_ctor_set(v___x_2757_, 1, v_e_2746_);
v___x_2758_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(v_numExtraArgs_2745_, v___x_2755_, v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v_fst_2760_; lean_object* v_snd_2761_; lean_object* v_proc_2762_; lean_object* v___x_2763_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
v_fst_2760_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_fst_2760_);
v_snd_2761_ = lean_ctor_get(v_a_2759_, 1);
lean_inc(v_snd_2761_);
lean_dec(v_a_2759_);
v_proc_2762_ = lean_ctor_get(v_s_2744_, 1);
lean_inc_ref(v_proc_2762_);
lean_dec_ref(v_s_2744_);
v___x_2763_ = l_Array_reverse___redArg(v_fst_2760_);
if (lean_obj_tag(v_proc_2762_) == 0)
{
lean_object* v_val_2764_; lean_object* v___x_2765_; 
v_val_2764_ = lean_ctor_get(v_proc_2762_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v_proc_2762_);
lean_inc(v_a_2753_);
lean_inc_ref(v_a_2752_);
lean_inc(v_a_2751_);
lean_inc_ref(v_a_2750_);
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
v___x_2765_ = lean_apply_9(v_val_2764_, v_snd_2761_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, lean_box(0));
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref(v___x_2765_);
v___x_2767_ = l_Lean_Meta_Simp_Step_addExtraArgs(v_a_2766_, v___x_2763_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
lean_dec_ref(v___x_2763_);
return v___x_2767_;
}
else
{
lean_dec_ref(v___x_2763_);
return v___x_2765_;
}
}
else
{
lean_object* v_val_2768_; lean_object* v___x_2769_; 
v_val_2768_ = lean_ctor_get(v_proc_2762_, 0);
lean_inc(v_val_2768_);
lean_dec_ref(v_proc_2762_);
lean_inc(v_a_2753_);
lean_inc_ref(v_a_2752_);
lean_inc(v_a_2751_);
lean_inc_ref(v_a_2750_);
lean_inc(v_a_2749_);
lean_inc_ref(v_a_2748_);
lean_inc(v_a_2747_);
v___x_2769_ = lean_apply_9(v_val_2768_, v_snd_2761_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, lean_box(0));
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref(v___x_2769_);
v___x_2771_ = l_Lean_TransformStep_toStep(v_a_2770_);
v___x_2772_ = l_Lean_Meta_Simp_Step_addExtraArgs(v___x_2771_, v___x_2763_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
lean_dec_ref(v___x_2763_);
return v___x_2772_;
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v___x_2763_);
v_a_2773_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2769_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2769_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v_s_2744_);
v_a_2781_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2758_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2758_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try___boxed(lean_object* v_s_2789_, lean_object* v_numExtraArgs_2790_, lean_object* v_e_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_Meta_Simp_SimprocEntry_try(v_s_2789_, v_numExtraArgs_2790_, v_e_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
lean_dec(v_a_2796_);
lean_dec_ref(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
lean_dec(v_a_2792_);
lean_dec(v_numExtraArgs_2790_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0(lean_object* v_upperBound_2801_, lean_object* v_inst_2802_, lean_object* v_R_2803_, lean_object* v_a_2804_, lean_object* v_b_2805_, lean_object* v_c_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(v_upperBound_2801_, v_a_2804_, v_b_2805_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___boxed(lean_object* v_upperBound_2816_, lean_object* v_inst_2817_, lean_object* v_R_2818_, lean_object* v_a_2819_, lean_object* v_b_2820_, lean_object* v_c_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0(v_upperBound_2816_, v_inst_2817_, v_R_2818_, v_a_2819_, v_b_2820_, v_c_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec(v_upperBound_2816_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD(lean_object* v_s_2833_, lean_object* v_numExtraArgs_2834_, lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2844_; lean_object* v_extraArgs_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2844_ = lean_unsigned_to_nat(0u);
v_extraArgs_2845_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_try___closed__0));
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v_extraArgs_2845_);
lean_ctor_set(v___x_2846_, 1, v_e_2835_);
v___x_2847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(v_numExtraArgs_2834_, v___x_2844_, v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_proc_2848_; 
v_proc_2848_ = lean_ctor_get(v_s_2833_, 1);
lean_inc_ref(v_proc_2848_);
lean_dec_ref(v_s_2833_);
if (lean_obj_tag(v_proc_2848_) == 0)
{
lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref(v_proc_2848_);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2847_, 0);
lean_dec(v_unused_2857_);
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
else
{
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2852_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2852_);
v___x_2854_ = v___x_2850_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v_val_2859_; lean_object* v_fst_2860_; lean_object* v_snd_2861_; lean_object* v___x_2862_; 
v_a_2858_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2847_);
v_val_2859_ = lean_ctor_get(v_proc_2848_, 0);
lean_inc(v_val_2859_);
lean_dec_ref(v_proc_2848_);
v_fst_2860_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_fst_2860_);
v_snd_2861_ = lean_ctor_get(v_a_2858_, 1);
lean_inc(v_snd_2861_);
lean_dec(v_a_2858_);
lean_inc(v_a_2842_);
lean_inc_ref(v_a_2841_);
lean_inc(v_a_2840_);
lean_inc_ref(v_a_2839_);
lean_inc(v_a_2838_);
lean_inc_ref(v_a_2837_);
lean_inc(v_a_2836_);
v___x_2862_ = lean_apply_9(v_val_2859_, v_snd_2861_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, lean_box(0));
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2872_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2867_ = l_Array_reverse___redArg(v_fst_2860_);
v___x_2868_ = l_Lean_Meta_Simp_DStep_addExtraArgs(v_a_2863_, v___x_2867_);
lean_dec_ref(v___x_2867_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2868_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_dec(v_fst_2860_);
return v___x_2862_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec_ref(v_s_2833_);
v_a_2873_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2847_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2847_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD___boxed(lean_object* v_s_2881_, lean_object* v_numExtraArgs_2882_, lean_object* v_e_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Meta_Simp_SimprocEntry_tryD(v_s_2881_, v_numExtraArgs_2882_, v_e_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec(v_numExtraArgs_2882_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(lean_object* v_cls_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_options_2899_; uint8_t v_hasTrace_2900_; 
v_options_2899_ = lean_ctor_get(v___y_2897_, 2);
v_hasTrace_2900_ = lean_ctor_get_uint8(v_options_2899_, sizeof(void*)*1);
if (v_hasTrace_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
lean_dec(v_cls_2896_);
v___x_2901_ = lean_box(v_hasTrace_2900_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
return v___x_2902_;
}
else
{
lean_object* v_inheritedTraceOptions_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v_inheritedTraceOptions_2903_ = lean_ctor_get(v___y_2897_, 13);
v___x_2904_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___closed__1));
v___x_2905_ = l_Lean_Name_append(v___x_2904_, v_cls_2896_);
v___x_2906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2903_, v_options_2899_, v___x_2905_);
lean_dec(v___x_2905_);
v___x_2907_ = lean_box(v___x_2906_);
v___x_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg___boxed(lean_object* v_cls_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v_cls_2909_, v___y_2910_);
lean_dec_ref(v___y_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0(lean_object* v_cls_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v_cls_2913_, v___y_2919_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___boxed(lean_object* v_cls_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0(v_cls_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1(lean_object* v_msgData_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; lean_object* v_env_2940_; lean_object* v___x_2941_; lean_object* v_mctx_2942_; lean_object* v_lctx_2943_; lean_object* v_options_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2939_ = lean_st_ref_get(v___y_2937_);
v_env_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc_ref(v_env_2940_);
lean_dec(v___x_2939_);
v___x_2941_ = lean_st_ref_get(v___y_2935_);
v_mctx_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc_ref(v_mctx_2942_);
lean_dec(v___x_2941_);
v_lctx_2943_ = lean_ctor_get(v___y_2934_, 2);
v_options_2944_ = lean_ctor_get(v___y_2936_, 2);
lean_inc_ref(v_options_2944_);
lean_inc_ref(v_lctx_2943_);
v___x_2945_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2945_, 0, v_env_2940_);
lean_ctor_set(v___x_2945_, 1, v_mctx_2942_);
lean_ctor_set(v___x_2945_, 2, v_lctx_2943_);
lean_ctor_set(v___x_2945_, 3, v_options_2944_);
v___x_2946_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v_msgData_2933_);
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1___boxed(lean_object* v_msgData_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1(v_msgData_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
return v_res_2954_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2955_; double v___x_2956_; 
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = lean_float_of_nat(v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(lean_object* v_cls_2960_, lean_object* v_msg_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v_ref_2967_; lean_object* v___x_2968_; lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3013_; 
v_ref_2967_ = lean_ctor_get(v___y_2964_, 5);
v___x_2968_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1(v_msg_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_3013_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3013_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v_traceState_2974_; lean_object* v_env_2975_; lean_object* v_nextMacroScope_2976_; lean_object* v_ngen_2977_; lean_object* v_auxDeclNGen_2978_; lean_object* v_cache_2979_; lean_object* v_messages_2980_; lean_object* v_infoState_2981_; lean_object* v_snapshotTasks_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3012_; 
v___x_2973_ = lean_st_ref_take(v___y_2965_);
v_traceState_2974_ = lean_ctor_get(v___x_2973_, 4);
v_env_2975_ = lean_ctor_get(v___x_2973_, 0);
v_nextMacroScope_2976_ = lean_ctor_get(v___x_2973_, 1);
v_ngen_2977_ = lean_ctor_get(v___x_2973_, 2);
v_auxDeclNGen_2978_ = lean_ctor_get(v___x_2973_, 3);
v_cache_2979_ = lean_ctor_get(v___x_2973_, 5);
v_messages_2980_ = lean_ctor_get(v___x_2973_, 6);
v_infoState_2981_ = lean_ctor_get(v___x_2973_, 7);
v_snapshotTasks_2982_ = lean_ctor_get(v___x_2973_, 8);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2984_ = v___x_2973_;
v_isShared_2985_ = v_isSharedCheck_3012_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_snapshotTasks_2982_);
lean_inc(v_infoState_2981_);
lean_inc(v_messages_2980_);
lean_inc(v_cache_2979_);
lean_inc(v_traceState_2974_);
lean_inc(v_auxDeclNGen_2978_);
lean_inc(v_ngen_2977_);
lean_inc(v_nextMacroScope_2976_);
lean_inc(v_env_2975_);
lean_dec(v___x_2973_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3012_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
uint64_t v_tid_2986_; lean_object* v_traces_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3011_; 
v_tid_2986_ = lean_ctor_get_uint64(v_traceState_2974_, sizeof(void*)*1);
v_traces_2987_ = lean_ctor_get(v_traceState_2974_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_traceState_2974_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2989_ = v_traceState_2974_;
v_isShared_2990_ = v_isSharedCheck_3011_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_traces_2987_);
lean_dec(v_traceState_2974_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3011_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; double v___x_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__0);
v___x_2993_ = 0;
v___x_2994_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__1));
v___x_2995_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2995_, 0, v_cls_2960_);
lean_ctor_set(v___x_2995_, 1, v___x_2991_);
lean_ctor_set(v___x_2995_, 2, v___x_2994_);
lean_ctor_set_float(v___x_2995_, sizeof(void*)*3, v___x_2992_);
lean_ctor_set_float(v___x_2995_, sizeof(void*)*3 + 8, v___x_2992_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*3 + 16, v___x_2993_);
v___x_2996_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___closed__2));
v___x_2997_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2995_);
lean_ctor_set(v___x_2997_, 1, v_a_2969_);
lean_ctor_set(v___x_2997_, 2, v___x_2996_);
lean_inc(v_ref_2967_);
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v_ref_2967_);
lean_ctor_set(v___x_2998_, 1, v___x_2997_);
v___x_2999_ = l_Lean_PersistentArray_push___redArg(v_traces_2987_, v___x_2998_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2999_);
v___x_3001_ = v___x_2989_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_2999_);
lean_ctor_set_uint64(v_reuseFailAlloc_3010_, sizeof(void*)*1, v_tid_2986_);
v___x_3001_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3003_; 
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 4, v___x_3001_);
v___x_3003_ = v___x_2984_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_env_2975_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_nextMacroScope_2976_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v_ngen_2977_);
lean_ctor_set(v_reuseFailAlloc_3009_, 3, v_auxDeclNGen_2978_);
lean_ctor_set(v_reuseFailAlloc_3009_, 4, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3009_, 5, v_cache_2979_);
lean_ctor_set(v_reuseFailAlloc_3009_, 6, v_messages_2980_);
lean_ctor_set(v_reuseFailAlloc_3009_, 7, v_infoState_2981_);
lean_ctor_set(v_reuseFailAlloc_3009_, 8, v_snapshotTasks_2982_);
v___x_3003_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v___x_3004_ = lean_st_ref_set(v___y_2965_, v___x_3003_);
v___x_3005_ = lean_box(0);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_3005_);
v___x_3007_ = v___x_2971_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg___boxed(lean_object* v_cls_3014_, lean_object* v_msg_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v_cls_3014_, v_msg_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
return v_res_3021_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__4));
v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
return v___x_3032_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__6));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2(lean_object* v_erased_3036_, uint8_t v_post_3037_, lean_object* v___x_3038_, lean_object* v_as_3039_, size_t v_sz_3040_, size_t v_i_3041_, lean_object* v_b_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
lean_object* v_a_3052_; uint8_t v___x_3056_; 
v___x_3056_ = lean_usize_dec_lt(v_i_3041_, v_sz_3040_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_dec_ref(v_erased_3036_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v_b_3042_);
return v___x_3057_;
}
else
{
lean_object* v_a_3058_; lean_object* v_snd_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3362_; 
v_a_3058_ = lean_array_uget(v_as_3039_, v_i_3041_);
v_snd_3059_ = lean_ctor_get(v_b_3042_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_b_3042_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v_b_3042_, 0);
lean_dec(v_unused_3363_);
v___x_3061_ = v_b_3042_;
v_isShared_3062_ = v_isSharedCheck_3362_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_snd_3059_);
lean_dec(v_b_3042_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3362_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_snd_3063_; lean_object* v_snd_3064_; lean_object* v_fst_3065_; lean_object* v_toSimprocOLeanEntry_3066_; lean_object* v_snd_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3360_; 
v_snd_3063_ = lean_ctor_get(v_snd_3059_, 1);
lean_inc(v_snd_3063_);
v_snd_3064_ = lean_ctor_get(v_snd_3063_, 1);
lean_inc(v_snd_3064_);
v_fst_3065_ = lean_ctor_get(v_a_3058_, 0);
lean_inc(v_fst_3065_);
v_toSimprocOLeanEntry_3066_ = lean_ctor_get(v_fst_3065_, 0);
v_snd_3067_ = lean_ctor_get(v_a_3058_, 1);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_a_3058_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; 
v_unused_3361_ = lean_ctor_get(v_a_3058_, 0);
lean_dec(v_unused_3361_);
v___x_3069_ = v_a_3058_;
v_isShared_3070_ = v_isSharedCheck_3360_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_snd_3067_);
lean_dec(v_a_3058_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3360_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_fst_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3358_; 
v_fst_3071_ = lean_ctor_get(v_snd_3059_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_snd_3059_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v_snd_3059_, 1);
lean_dec(v_unused_3359_);
v___x_3073_ = v_snd_3059_;
v_isShared_3074_ = v_isSharedCheck_3358_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_fst_3071_);
lean_dec(v_snd_3059_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3358_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_fst_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3356_; 
v_fst_3075_ = lean_ctor_get(v_snd_3063_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_snd_3063_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; 
v_unused_3357_ = lean_ctor_get(v_snd_3063_, 1);
lean_dec(v_unused_3357_);
v___x_3077_ = v_snd_3063_;
v_isShared_3078_ = v_isSharedCheck_3356_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_fst_3075_);
lean_dec(v_snd_3063_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3356_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v_fst_3079_; lean_object* v_snd_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3355_; 
v_fst_3079_ = lean_ctor_get(v_snd_3064_, 0);
v_snd_3080_ = lean_ctor_get(v_snd_3064_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_snd_3064_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3082_ = v_snd_3064_;
v_isShared_3083_ = v_isSharedCheck_3355_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_snd_3080_);
lean_inc(v_fst_3079_);
lean_dec(v_snd_3064_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3355_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_declName_3084_; lean_object* v___x_3085_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; uint8_t v___x_3104_; 
v_declName_3084_ = lean_ctor_get(v_toSimprocOLeanEntry_3066_, 0);
v___x_3085_ = lean_box(0);
lean_inc_ref(v_erased_3036_);
v___x_3104_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_erased_3036_, v_declName_3084_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
lean_inc(v_declName_3084_);
lean_inc(v_fst_3071_);
v___x_3105_ = l_Lean_Meta_Simp_SimprocEntry_try(v_fst_3065_, v_snd_3067_, v_fst_3071_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v_snd_3067_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v___x_3105_);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = lean_nat_dec_eq(v___x_3038_, v___x_3107_);
switch(lean_obj_tag(v_a_3106_))
{
case 0:
{
lean_object* v_r_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3186_; 
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_r_3109_ = lean_ctor_get(v_a_3106_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3111_ = v_a_3106_;
v_isShared_3112_ = v_isSharedCheck_3186_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_r_3109_);
lean_dec(v_a_3106_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3186_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3158_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3157_, v___y_3048_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; uint8_t v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref(v___x_3158_);
v___x_3160_ = lean_unbox(v_a_3159_);
lean_dec(v_a_3159_);
if (v___x_3160_ == 0)
{
v___y_3114_ = v___y_3045_;
v___y_3115_ = v___y_3046_;
v___y_3116_ = v___y_3047_;
v___y_3117_ = v___y_3048_;
v___y_3118_ = v___y_3049_;
goto v___jp_3113_;
}
else
{
lean_object* v_expr_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_expr_3161_ = lean_ctor_get(v_r_3109_, 0);
v___x_3162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
lean_inc(v_fst_3071_);
v___x_3163_ = l_Lean_MessageData_ofExpr(v_fst_3071_);
v___x_3164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3162_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3164_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
lean_inc_ref(v_expr_3161_);
v___x_3167_ = l_Lean_MessageData_ofExpr(v_expr_3161_);
v___x_3168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3157_, v___x_3168_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref(v___x_3169_);
v___y_3114_ = v___y_3045_;
v___y_3115_ = v___y_3046_;
v___y_3116_ = v___y_3047_;
v___y_3117_ = v___y_3048_;
v___y_3118_ = v___y_3049_;
goto v___jp_3113_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_del_object(v___x_3111_);
lean_dec_ref(v_r_3109_);
lean_dec(v_declName_3084_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_del_object(v___x_3111_);
lean_dec_ref(v_r_3109_);
lean_dec(v_declName_3084_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3178_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3158_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3158_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
v___jp_3113_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3119_, 0, v_declName_3084_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*1, v_post_3037_);
lean_ctor_set_uint8(v___x_3119_, sizeof(void*)*1 + 1, v___x_3108_);
v___x_3120_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3119_, v___y_3114_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3120_) == 0)
{
uint8_t v___x_3121_; lean_object* v___x_3122_; 
lean_dec_ref(v___x_3120_);
v___x_3121_ = lean_unbox(v_snd_3080_);
lean_inc(v_fst_3075_);
v___x_3122_ = l_Lean_Meta_Simp_mkEqTransOptProofResult(v_fst_3075_, v___x_3121_, v_r_3109_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3140_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3140_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3140_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v_a_3123_);
v___x_3128_ = v___x_3111_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_snd_3080_);
lean_ctor_set(v___x_3069_, 0, v_fst_3079_);
v___x_3131_ = v___x_3069_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_snd_3080_);
v___x_3131_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_fst_3075_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v_fst_3071_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3129_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3134_);
v___x_3136_ = v___x_3125_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_del_object(v___x_3111_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3141_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3122_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3122_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_del_object(v___x_3111_);
lean_dec_ref(v_r_3109_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3149_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3120_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3120_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
case 1:
{
lean_object* v_e_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3264_; 
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_e_3187_ = lean_ctor_get(v_a_3106_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_3106_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3189_ = v_a_3106_;
v_isShared_3190_ = v_isSharedCheck_3264_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_e_3187_);
lean_dec(v_a_3106_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3264_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3236_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3235_, v___y_3048_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; uint8_t v___x_3238_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref(v___x_3236_);
v___x_3238_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3238_ == 0)
{
v___y_3192_ = v___y_3045_;
v___y_3193_ = v___y_3046_;
v___y_3194_ = v___y_3047_;
v___y_3195_ = v___y_3048_;
v___y_3196_ = v___y_3049_;
goto v___jp_3191_;
}
else
{
lean_object* v_expr_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v_expr_3239_ = lean_ctor_get(v_e_3187_, 0);
v___x_3240_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
lean_inc(v_fst_3071_);
v___x_3241_ = l_Lean_MessageData_ofExpr(v_fst_3071_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
lean_inc_ref(v_expr_3239_);
v___x_3245_ = l_Lean_MessageData_ofExpr(v_expr_3239_);
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3244_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3235_, v___x_3246_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_dec_ref(v___x_3247_);
v___y_3192_ = v___y_3045_;
v___y_3193_ = v___y_3046_;
v___y_3194_ = v___y_3047_;
v___y_3195_ = v___y_3048_;
v___y_3196_ = v___y_3049_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_del_object(v___x_3189_);
lean_dec_ref(v_e_3187_);
lean_dec(v_declName_3084_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3247_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3247_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_del_object(v___x_3189_);
lean_dec_ref(v_e_3187_);
lean_dec(v_declName_3084_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3256_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3236_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3236_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
v___jp_3191_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3197_, 0, v_declName_3084_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*1, v_post_3037_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*1 + 1, v___x_3108_);
v___x_3198_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3197_, v___y_3192_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3198_) == 0)
{
uint8_t v___x_3199_; lean_object* v___x_3200_; 
lean_dec_ref(v___x_3198_);
v___x_3199_ = lean_unbox(v_snd_3080_);
lean_inc(v_fst_3075_);
v___x_3200_ = l_Lean_Meta_Simp_mkEqTransOptProofResult(v_fst_3075_, v___x_3199_, v_e_3187_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3218_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3218_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3218_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v_a_3201_);
v___x_3206_ = v___x_3189_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_snd_3080_);
lean_ctor_set(v___x_3069_, 0, v_fst_3079_);
v___x_3209_ = v___x_3069_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v_snd_3080_);
v___x_3209_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3210_, 0, v_fst_3075_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3211_, 0, v_fst_3071_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3207_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v___x_3212_);
v___x_3214_ = v___x_3203_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_del_object(v___x_3189_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3219_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3200_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3200_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_del_object(v___x_3189_);
lean_dec_ref(v_e_3187_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_dec(v_fst_3075_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
v_a_3227_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3198_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3198_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
}
default: 
{
lean_object* v_e_x3f_3265_; 
v_e_x3f_3265_ = lean_ctor_get(v_a_3106_, 0);
lean_inc(v_e_x3f_3265_);
lean_dec_ref(v_a_3106_);
if (lean_obj_tag(v_e_x3f_3265_) == 0)
{
lean_object* v___x_3267_; 
lean_dec(v_declName_3084_);
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_snd_3080_);
lean_ctor_set(v___x_3069_, 0, v_fst_3079_);
v___x_3267_ = v___x_3069_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_snd_3080_);
v___x_3267_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v_fst_3075_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v_fst_3071_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3085_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v_a_3052_ = v___x_3270_;
goto v___jp_3051_;
}
}
else
{
lean_object* v_val_3272_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
lean_dec(v_fst_3079_);
lean_del_object(v___x_3069_);
v_val_3272_ = lean_ctor_get(v_e_x3f_3265_, 0);
lean_inc(v_val_3272_);
lean_dec_ref(v_e_x3f_3265_);
v___x_3304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3305_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3304_, v___y_3048_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; uint8_t v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = lean_unbox(v_a_3306_);
lean_dec(v_a_3306_);
if (v___x_3307_ == 0)
{
lean_dec(v_fst_3071_);
v___y_3274_ = v___y_3045_;
v___y_3275_ = v___y_3046_;
v___y_3276_ = v___y_3047_;
v___y_3277_ = v___y_3048_;
v___y_3278_ = v___y_3049_;
goto v___jp_3273_;
}
else
{
lean_object* v_expr_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_expr_3308_ = lean_ctor_get(v_val_3272_, 0);
v___x_3309_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
v___x_3310_ = l_Lean_MessageData_ofExpr(v_fst_3071_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
lean_inc_ref(v_expr_3308_);
v___x_3314_ = l_Lean_MessageData_ofExpr(v_expr_3308_);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3304_, v___x_3315_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_dec_ref(v___x_3316_);
v___y_3274_ = v___y_3045_;
v___y_3275_ = v___y_3046_;
v___y_3276_ = v___y_3047_;
v___y_3277_ = v___y_3048_;
v___y_3278_ = v___y_3049_;
goto v___jp_3273_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_val_3272_);
lean_dec(v_declName_3084_);
lean_del_object(v___x_3082_);
lean_dec(v_snd_3080_);
lean_del_object(v___x_3077_);
lean_dec(v_fst_3075_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_val_3272_);
lean_dec(v_declName_3084_);
lean_del_object(v___x_3082_);
lean_dec(v_snd_3080_);
lean_del_object(v___x_3077_);
lean_dec(v_fst_3075_);
lean_del_object(v___x_3073_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_a_3325_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3305_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3305_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
v___jp_3273_:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3279_, 0, v_declName_3084_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*1, v_post_3037_);
lean_ctor_set_uint8(v___x_3279_, sizeof(void*)*1 + 1, v___x_3108_);
v___x_3280_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3279_, v___y_3274_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_expr_3281_; lean_object* v_proof_x3f_3282_; uint8_t v_cache_3283_; lean_object* v___x_3284_; 
lean_dec_ref(v___x_3280_);
v_expr_3281_ = lean_ctor_get(v_val_3272_, 0);
lean_inc_ref(v_expr_3281_);
v_proof_x3f_3282_ = lean_ctor_get(v_val_3272_, 1);
lean_inc(v_proof_x3f_3282_);
v_cache_3283_ = lean_ctor_get_uint8(v_val_3272_, sizeof(void*)*2);
lean_dec(v_val_3272_);
v___x_3284_ = l_Lean_Meta_mkEqTrans_x3f(v_fst_3075_, v_proof_x3f_3282_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3284_) == 0)
{
uint8_t v___x_3285_; 
v___x_3285_ = lean_unbox(v_snd_3080_);
lean_dec(v_snd_3080_);
if (v___x_3285_ == 0)
{
lean_object* v_a_3286_; 
v_a_3286_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3286_);
lean_dec_ref(v___x_3284_);
v___y_3087_ = v_expr_3281_;
v___y_3088_ = v_a_3286_;
v___y_3089_ = v___x_3108_;
goto v___jp_3086_;
}
else
{
lean_object* v_a_3287_; 
v_a_3287_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3284_);
v___y_3087_ = v_expr_3281_;
v___y_3088_ = v_a_3287_;
v___y_3089_ = v_cache_3283_;
goto v___jp_3086_;
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec_ref(v_expr_3281_);
lean_del_object(v___x_3082_);
lean_dec(v_snd_3080_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_a_3288_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3284_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3284_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_val_3272_);
lean_del_object(v___x_3082_);
lean_dec(v_snd_3080_);
lean_del_object(v___x_3077_);
lean_dec(v_fst_3075_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_a_3296_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3280_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3280_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
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
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v_declName_3084_);
lean_del_object(v___x_3082_);
lean_dec(v_snd_3080_);
lean_dec(v_fst_3079_);
lean_del_object(v___x_3077_);
lean_dec(v_fst_3075_);
lean_del_object(v___x_3073_);
lean_dec(v_fst_3071_);
lean_del_object(v___x_3069_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_erased_3036_);
v_a_3333_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3105_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3105_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3352_; 
lean_del_object(v___x_3082_);
lean_del_object(v___x_3077_);
lean_del_object(v___x_3073_);
lean_dec(v_snd_3067_);
lean_del_object(v___x_3061_);
v_isSharedCheck_3352_ = !lean_is_exclusive(v_fst_3065_);
if (v_isSharedCheck_3352_ == 0)
{
lean_object* v_unused_3353_; lean_object* v_unused_3354_; 
v_unused_3353_ = lean_ctor_get(v_fst_3065_, 1);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_fst_3065_, 0);
lean_dec(v_unused_3354_);
v___x_3342_ = v_fst_3065_;
v_isShared_3343_ = v_isSharedCheck_3352_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_fst_3065_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3352_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_snd_3080_);
lean_ctor_set(v___x_3069_, 0, v_fst_3079_);
v___x_3345_ = v___x_3069_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_fst_3079_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_snd_3080_);
v___x_3345_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v___x_3345_);
lean_ctor_set(v___x_3342_, 0, v_fst_3075_);
v___x_3347_ = v___x_3342_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_fst_3075_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v_fst_3071_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3085_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v_a_3052_ = v___x_3349_;
goto v___jp_3051_;
}
}
}
}
v___jp_3086_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3090_ = lean_box(v___x_3056_);
v___x_3091_ = lean_box(v___y_3089_);
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 1, v___x_3091_);
lean_ctor_set(v___x_3082_, 0, v___x_3090_);
v___x_3093_ = v___x_3082_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3095_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_3093_);
lean_ctor_set(v___x_3077_, 0, v___y_3088_);
v___x_3095_ = v___x_3077_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___y_3088_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
lean_object* v___x_3097_; 
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 1, v___x_3095_);
lean_ctor_set(v___x_3073_, 0, v___y_3087_);
v___x_3097_ = v___x_3073_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___y_3087_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3099_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 1, v___x_3097_);
lean_ctor_set(v___x_3061_, 0, v___x_3085_);
v___x_3099_ = v___x_3061_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
v_a_3052_ = v___x_3099_;
goto v___jp_3051_;
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
v___jp_3051_:
{
size_t v___x_3053_; size_t v___x_3054_; 
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = lean_usize_add(v_i_3041_, v___x_3053_);
v_i_3041_ = v___x_3054_;
v_b_3042_ = v_a_3052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___boxed(lean_object* v_erased_3364_, lean_object* v_post_3365_, lean_object* v___x_3366_, lean_object* v_as_3367_, lean_object* v_sz_3368_, lean_object* v_i_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
uint8_t v_post_boxed_3379_; size_t v_sz_boxed_3380_; size_t v_i_boxed_3381_; lean_object* v_res_3382_; 
v_post_boxed_3379_ = lean_unbox(v_post_3365_);
v_sz_boxed_3380_ = lean_unbox_usize(v_sz_3368_);
lean_dec(v_sz_3368_);
v_i_boxed_3381_ = lean_unbox_usize(v_i_3369_);
lean_dec(v_i_3369_);
v_res_3382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2(v_erased_3364_, v_post_boxed_3379_, v___x_3366_, v_as_3367_, v_sz_boxed_3380_, v_i_boxed_3381_, v_b_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v_as_3367_);
lean_dec(v___x_3366_);
return v_res_3382_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__2(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__1));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simprocCore___closed__4(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__3));
v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore(uint8_t v_post_3395_, lean_object* v_s_3396_, lean_object* v_erased_3397_, lean_object* v_e_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v___y_3411_; lean_object* v_a_3433_; lean_object* v_indexConfig_3487_; lean_object* v_config_3488_; uint8_t v_trackZetaDelta_3489_; lean_object* v_zetaDeltaSet_3490_; lean_object* v_lctx_3491_; lean_object* v_localInstances_3492_; lean_object* v_defEqCtx_x3f_3493_; lean_object* v_synthPendingDepth_3494_; lean_object* v_canUnfold_x3f_3495_; uint8_t v_univApprox_3496_; uint8_t v_inTypeClassResolution_3497_; uint8_t v_cacheInferType_3498_; uint64_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v_indexConfig_3487_ = lean_ctor_get(v_a_3400_, 4);
v_config_3488_ = lean_ctor_get(v_indexConfig_3487_, 0);
v_trackZetaDelta_3489_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7);
v_zetaDeltaSet_3490_ = lean_ctor_get(v_a_3402_, 1);
v_lctx_3491_ = lean_ctor_get(v_a_3402_, 2);
v_localInstances_3492_ = lean_ctor_get(v_a_3402_, 3);
v_defEqCtx_x3f_3493_ = lean_ctor_get(v_a_3402_, 4);
v_synthPendingDepth_3494_ = lean_ctor_get(v_a_3402_, 5);
v_canUnfold_x3f_3495_ = lean_ctor_get(v_a_3402_, 6);
v_univApprox_3496_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3497_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7 + 2);
v_cacheInferType_3498_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7 + 3);
v___x_3499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3488_);
lean_inc_ref(v_config_3488_);
v___x_3500_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3500_, 0, v_config_3488_);
lean_ctor_set_uint64(v___x_3500_, sizeof(void*)*1, v___x_3499_);
lean_inc(v_canUnfold_x3f_3495_);
lean_inc(v_synthPendingDepth_3494_);
lean_inc(v_defEqCtx_x3f_3493_);
lean_inc_ref(v_localInstances_3492_);
lean_inc_ref(v_lctx_3491_);
lean_inc(v_zetaDeltaSet_3490_);
v___x_3501_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v_zetaDeltaSet_3490_);
lean_ctor_set(v___x_3501_, 2, v_lctx_3491_);
lean_ctor_set(v___x_3501_, 3, v_localInstances_3492_);
lean_ctor_set(v___x_3501_, 4, v_defEqCtx_x3f_3493_);
lean_ctor_set(v___x_3501_, 5, v_synthPendingDepth_3494_);
lean_ctor_set(v___x_3501_, 6, v_canUnfold_x3f_3495_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*7, v_trackZetaDelta_3489_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*7 + 1, v_univApprox_3496_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3497_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*7 + 3, v_cacheInferType_3498_);
lean_inc_ref(v_e_3398_);
v___x_3502_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_s_3396_, v_e_3398_, v___x_3501_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec_ref(v___x_3501_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref(v___x_3502_);
v_a_3433_ = v_a_3503_;
goto v___jp_3432_;
}
else
{
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3502_);
v_a_3433_ = v_a_3504_;
goto v___jp_3432_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v_e_3398_);
lean_dec_ref(v_erased_3397_);
v_a_3505_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3502_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3502_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
v___jp_3407_:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__0));
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
v___jp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v_a_3414_; uint8_t v___x_3415_; 
v___x_3412_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3413_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3412_, v_a_3404_);
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref(v___x_3413_);
v___x_3415_ = lean_unbox(v_a_3414_);
lean_dec(v_a_3414_);
if (v___x_3415_ == 0)
{
lean_dec_ref(v___y_3411_);
lean_dec_ref(v_e_3398_);
goto v___jp_3407_;
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3416_ = lean_obj_once(&l_Lean_Meta_Simp_simprocCore___closed__2, &l_Lean_Meta_Simp_simprocCore___closed__2_once, _init_l_Lean_Meta_Simp_simprocCore___closed__2);
v___x_3417_ = l_Lean_stringToMessageData(v___y_3411_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = lean_obj_once(&l_Lean_Meta_Simp_simprocCore___closed__4, &l_Lean_Meta_Simp_simprocCore___closed__4_once, _init_l_Lean_Meta_Simp_simprocCore___closed__4);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_MessageData_ofExpr(v_e_3398_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3412_, v___x_3422_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_dec_ref(v___x_3423_);
goto v___jp_3407_;
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
v___jp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v___x_3434_ = lean_array_get_size(v_a_3433_);
v___x_3435_ = lean_unsigned_to_nat(0u);
v___x_3436_ = lean_nat_dec_eq(v___x_3434_, v___x_3435_);
if (v___x_3436_ == 0)
{
uint8_t v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; size_t v_sz_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3437_ = 1;
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_box(v___x_3436_);
v___x_3440_ = lean_box(v___x_3437_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3438_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
v___x_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3443_, 0, v_e_3398_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3438_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v_sz_3445_ = lean_array_size(v_a_3433_);
v___x_3446_ = ((size_t)0ULL);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2(v_erased_3397_, v_post_3395_, v___x_3434_, v_a_3433_, v_sz_3445_, v___x_3446_, v___x_3444_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec_ref(v_a_3433_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3476_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3476_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3476_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v_fst_3452_; 
v_fst_3452_ = lean_ctor_get(v_a_3448_, 0);
if (lean_obj_tag(v_fst_3452_) == 0)
{
lean_object* v_snd_3453_; lean_object* v_snd_3454_; lean_object* v_snd_3455_; lean_object* v_fst_3456_; uint8_t v___x_3457_; 
v_snd_3453_ = lean_ctor_get(v_a_3448_, 1);
lean_inc(v_snd_3453_);
lean_dec(v_a_3448_);
v_snd_3454_ = lean_ctor_get(v_snd_3453_, 1);
lean_inc(v_snd_3454_);
v_snd_3455_ = lean_ctor_get(v_snd_3454_, 1);
lean_inc(v_snd_3455_);
v_fst_3456_ = lean_ctor_get(v_snd_3455_, 0);
v___x_3457_ = lean_unbox(v_fst_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_dec(v_snd_3455_);
lean_dec(v_snd_3454_);
lean_dec(v_snd_3453_);
v___x_3458_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__5));
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3458_);
v___x_3460_ = v___x_3450_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
else
{
lean_object* v_fst_3462_; lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v_fst_3462_ = lean_ctor_get(v_snd_3453_, 0);
lean_inc(v_fst_3462_);
lean_dec(v_snd_3453_);
v_fst_3463_ = lean_ctor_get(v_snd_3454_, 0);
lean_inc(v_fst_3463_);
lean_dec(v_snd_3454_);
v_snd_3464_ = lean_ctor_get(v_snd_3455_, 1);
lean_inc(v_snd_3464_);
lean_dec(v_snd_3455_);
v___x_3465_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3465_, 0, v_fst_3462_);
lean_ctor_set(v___x_3465_, 1, v_fst_3463_);
v___x_3466_ = lean_unbox(v_snd_3464_);
lean_dec(v_snd_3464_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*2, v___x_3466_);
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
v___x_3468_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3468_);
v___x_3470_ = v___x_3450_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
else
{
lean_object* v_val_3472_; lean_object* v___x_3474_; 
lean_inc_ref(v_fst_3452_);
lean_dec(v_a_3448_);
v_val_3472_ = lean_ctor_get(v_fst_3452_, 0);
lean_inc(v_val_3472_);
lean_dec_ref(v_fst_3452_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v_val_3472_);
v___x_3474_ = v___x_3450_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_val_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_a_3477_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3447_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3447_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_dec_ref(v_a_3433_);
lean_dec_ref(v_erased_3397_);
if (v_post_3395_ == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__6));
v___y_3411_ = v___x_3485_;
goto v___jp_3410_;
}
else
{
lean_object* v___x_3486_; 
v___x_3486_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__7));
v___y_3411_ = v___x_3486_;
goto v___jp_3410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object* v_post_3513_, lean_object* v_s_3514_, lean_object* v_erased_3515_, lean_object* v_e_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
uint8_t v_post_boxed_3525_; lean_object* v_res_3526_; 
v_post_boxed_3525_ = lean_unbox(v_post_3513_);
v_res_3526_ = l_Lean_Meta_Simp_simprocCore(v_post_boxed_3525_, v_s_3514_, v_erased_3515_, v_e_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1(lean_object* v_cls_3527_, lean_object* v_msg_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v_cls_3527_, v_msg_3528_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___boxed(lean_object* v_cls_3538_, lean_object* v_msg_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1(v_cls_3538_, v_msg_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(lean_object* v_erased_3549_, uint8_t v_post_3550_, lean_object* v___x_3551_, lean_object* v_as_3552_, size_t v_sz_3553_, size_t v_i_3554_, lean_object* v_b_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_a_3565_; uint8_t v___x_3569_; 
v___x_3569_ = lean_usize_dec_lt(v_i_3554_, v_sz_3553_);
if (v___x_3569_ == 0)
{
lean_object* v___x_3570_; 
lean_dec_ref(v_erased_3549_);
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v_b_3555_);
return v___x_3570_;
}
else
{
lean_object* v_a_3571_; lean_object* v_snd_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3774_; 
v_a_3571_ = lean_array_uget(v_as_3552_, v_i_3554_);
v_snd_3572_ = lean_ctor_get(v_b_3555_, 1);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_b_3555_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v_b_3555_, 0);
lean_dec(v_unused_3775_);
v___x_3574_ = v_b_3555_;
v_isShared_3575_ = v_isSharedCheck_3774_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_snd_3572_);
lean_dec(v_b_3555_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3774_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_fst_3576_; lean_object* v_toSimprocOLeanEntry_3577_; lean_object* v_snd_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3772_; 
v_fst_3576_ = lean_ctor_get(v_a_3571_, 0);
lean_inc(v_fst_3576_);
v_toSimprocOLeanEntry_3577_ = lean_ctor_get(v_fst_3576_, 0);
v_snd_3578_ = lean_ctor_get(v_a_3571_, 1);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_a_3571_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; 
v_unused_3773_ = lean_ctor_get(v_a_3571_, 0);
lean_dec(v_unused_3773_);
v___x_3580_ = v_a_3571_;
v_isShared_3581_ = v_isSharedCheck_3772_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_snd_3578_);
lean_dec(v_a_3571_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3772_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_fst_3582_; lean_object* v_snd_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3771_; 
v_fst_3582_ = lean_ctor_get(v_snd_3572_, 0);
v_snd_3583_ = lean_ctor_get(v_snd_3572_, 1);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_snd_3572_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3585_ = v_snd_3572_;
v_isShared_3586_ = v_isSharedCheck_3771_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_snd_3583_);
lean_inc(v_fst_3582_);
lean_dec(v_snd_3572_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3771_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v_declName_3587_; lean_object* v___x_3588_; uint8_t v___x_3589_; 
v_declName_3587_ = lean_ctor_get(v_toSimprocOLeanEntry_3577_, 0);
lean_inc(v_declName_3587_);
v___x_3588_ = lean_box(0);
lean_inc_ref(v_erased_3549_);
v___x_3589_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_erased_3549_, v_declName_3587_);
if (v___x_3589_ == 0)
{
lean_object* v___x_3590_; 
lean_inc(v_fst_3582_);
v___x_3590_ = l_Lean_Meta_Simp_SimprocEntry_tryD(v_fst_3576_, v_snd_3578_, v_fst_3582_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v_snd_3578_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = lean_unsigned_to_nat(0u);
v___x_3593_ = lean_nat_dec_eq(v___x_3551_, v___x_3592_);
switch(lean_obj_tag(v_a_3591_))
{
case 0:
{
lean_object* v_e_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
lean_del_object(v___x_3580_);
lean_dec_ref(v_erased_3549_);
v_e_3650_ = lean_ctor_get(v_a_3591_, 0);
v___x_3651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3652_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3651_, v___y_3561_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; uint8_t v___x_3654_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = lean_unbox(v_a_3653_);
lean_dec(v_a_3653_);
if (v___x_3654_ == 0)
{
v___y_3595_ = v___y_3558_;
v___y_3596_ = v___y_3561_;
v___y_3597_ = v___y_3562_;
goto v___jp_3594_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3655_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
lean_inc(v_fst_3582_);
v___x_3656_ = l_Lean_MessageData_ofExpr(v_fst_3582_);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v___x_3658_);
lean_inc_ref(v_e_3650_);
v___x_3660_ = l_Lean_MessageData_ofExpr(v_e_3650_);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3651_, v___x_3661_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_dec_ref(v___x_3662_);
v___y_3595_ = v___y_3558_;
v___y_3596_ = v___y_3561_;
v___y_3597_ = v___y_3562_;
goto v___jp_3594_;
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec_ref(v_a_3591_);
lean_dec(v_declName_3587_);
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3574_);
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec_ref(v_a_3591_);
lean_dec(v_declName_3587_);
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3574_);
v_a_3671_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3652_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3652_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
case 1:
{
lean_object* v_e_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_del_object(v___x_3585_);
lean_del_object(v___x_3574_);
lean_dec_ref(v_erased_3549_);
v_e_3679_ = lean_ctor_get(v_a_3591_, 0);
v___x_3680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3681_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3680_, v___y_3561_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; uint8_t v___x_3683_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_a_3682_);
lean_dec_ref(v___x_3681_);
v___x_3683_ = lean_unbox(v_a_3682_);
lean_dec(v_a_3682_);
if (v___x_3683_ == 0)
{
v___y_3624_ = v___y_3558_;
v___y_3625_ = v___y_3561_;
v___y_3626_ = v___y_3562_;
goto v___jp_3623_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
lean_inc(v_fst_3582_);
v___x_3685_ = l_Lean_MessageData_ofExpr(v_fst_3582_);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
lean_inc_ref(v_e_3679_);
v___x_3689_ = l_Lean_MessageData_ofExpr(v_e_3679_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3680_, v___x_3690_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_dec_ref(v___x_3691_);
v___y_3624_ = v___y_3558_;
v___y_3625_ = v___y_3561_;
v___y_3626_ = v___y_3562_;
goto v___jp_3623_;
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v_a_3591_);
lean_dec(v_declName_3587_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3580_);
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec_ref(v_a_3591_);
lean_dec(v_declName_3587_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3580_);
v_a_3700_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3681_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3681_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
default: 
{
lean_object* v_e_x3f_3708_; 
lean_del_object(v___x_3585_);
lean_del_object(v___x_3580_);
lean_del_object(v___x_3574_);
v_e_x3f_3708_ = lean_ctor_get(v_a_3591_, 0);
lean_inc(v_e_x3f_3708_);
lean_dec_ref(v_a_3591_);
if (lean_obj_tag(v_e_x3f_3708_) == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_dec(v_declName_3587_);
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_fst_3582_);
lean_ctor_set(v___x_3709_, 1, v_snd_3583_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3588_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v_a_3565_ = v___x_3710_;
goto v___jp_3564_;
}
else
{
lean_object* v_val_3711_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_snd_3583_);
v_val_3711_ = lean_ctor_get(v_e_x3f_3708_, 0);
lean_inc(v_val_3711_);
lean_dec_ref(v_e_x3f_3708_);
v___x_3729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3730_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3729_, v___y_3561_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; uint8_t v___x_3732_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = lean_unbox(v_a_3731_);
lean_dec(v_a_3731_);
if (v___x_3732_ == 0)
{
lean_dec(v_fst_3582_);
v___y_3713_ = v___y_3558_;
v___y_3714_ = v___y_3561_;
v___y_3715_ = v___y_3562_;
goto v___jp_3712_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3733_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
v___x_3734_ = l_Lean_MessageData_ofExpr(v_fst_3582_);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3735_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
lean_inc(v_val_3711_);
v___x_3738_ = l_Lean_MessageData_ofExpr(v_val_3711_);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3737_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3729_, v___x_3739_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_dec_ref(v___x_3740_);
v___y_3713_ = v___y_3558_;
v___y_3714_ = v___y_3561_;
v___y_3715_ = v___y_3562_;
goto v___jp_3712_;
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec(v_val_3711_);
lean_dec(v_declName_3587_);
lean_dec_ref(v_erased_3549_);
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_val_3711_);
lean_dec(v_declName_3587_);
lean_dec(v_fst_3582_);
lean_dec_ref(v_erased_3549_);
v_a_3749_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3730_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3730_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
v___jp_3712_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3716_, 0, v_declName_3587_);
lean_ctor_set_uint8(v___x_3716_, sizeof(void*)*1, v_post_3550_);
lean_ctor_set_uint8(v___x_3716_, sizeof(void*)*1 + 1, v___x_3593_);
v___x_3717_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3716_, v___y_3713_, v___y_3714_, v___y_3715_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_dec_ref(v___x_3717_);
v___x_3718_ = lean_box(v___x_3569_);
v___x_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3719_, 0, v_val_3711_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3588_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v_a_3565_ = v___x_3720_;
goto v___jp_3564_;
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec(v_val_3711_);
lean_dec_ref(v_erased_3549_);
v_a_3721_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3717_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3717_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
}
}
v___jp_3594_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3598_, 0, v_declName_3587_);
lean_ctor_set_uint8(v___x_3598_, sizeof(void*)*1, v_post_3550_);
lean_ctor_set_uint8(v___x_3598_, sizeof(void*)*1 + 1, v___x_3593_);
v___x_3599_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3598_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3613_; 
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v___x_3599_, 0);
lean_dec(v_unused_3614_);
v___x_3601_ = v___x_3599_;
v_isShared_3602_ = v_isSharedCheck_3613_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v___x_3599_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3613_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v_a_3591_);
if (v_isShared_3586_ == 0)
{
v___x_3605_ = v___x_3585_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_snd_3583_);
v___x_3605_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3607_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v___x_3605_);
lean_ctor_set(v___x_3574_, 0, v___x_3603_);
v___x_3607_ = v___x_3574_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3607_);
v___x_3609_ = v___x_3601_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_a_3591_);
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3574_);
v_a_3615_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3599_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3599_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
v___jp_3623_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3627_, 0, v_declName_3587_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*1, v_post_3550_);
lean_ctor_set_uint8(v___x_3627_, sizeof(void*)*1 + 1, v___x_3593_);
v___x_3628_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3627_, v___y_3624_, v___y_3625_, v___y_3626_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3640_; 
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v___x_3628_, 0);
lean_dec(v_unused_3641_);
v___x_3630_ = v___x_3628_;
v_isShared_3631_ = v_isSharedCheck_3640_;
goto v_resetjp_3629_;
}
else
{
lean_dec(v___x_3628_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3640_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_a_3591_);
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v_snd_3583_);
lean_ctor_set(v___x_3580_, 0, v_fst_3582_);
v___x_3634_ = v___x_3580_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_snd_3583_);
v___x_3634_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3632_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3635_);
v___x_3637_ = v___x_3630_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec(v_a_3591_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3580_);
v_a_3642_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3628_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3628_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_declName_3587_);
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3580_);
lean_del_object(v___x_3574_);
lean_dec_ref(v_erased_3549_);
v_a_3757_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3590_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3590_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v___x_3766_; 
lean_dec(v_declName_3587_);
lean_del_object(v___x_3580_);
lean_dec(v_snd_3578_);
lean_dec(v_fst_3576_);
if (v_isShared_3586_ == 0)
{
v___x_3766_ = v___x_3585_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_snd_3583_);
v___x_3766_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3768_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v___x_3766_);
lean_ctor_set(v___x_3574_, 0, v___x_3588_);
v___x_3768_ = v___x_3574_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
v_a_3565_ = v___x_3768_;
goto v___jp_3564_;
}
}
}
}
}
}
}
v___jp_3564_:
{
size_t v___x_3566_; size_t v___x_3567_; 
v___x_3566_ = ((size_t)1ULL);
v___x_3567_ = lean_usize_add(v_i_3554_, v___x_3566_);
v_i_3554_ = v___x_3567_;
v_b_3555_ = v_a_3565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0___boxed(lean_object* v_erased_3776_, lean_object* v_post_3777_, lean_object* v___x_3778_, lean_object* v_as_3779_, lean_object* v_sz_3780_, lean_object* v_i_3781_, lean_object* v_b_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_post_boxed_3791_; size_t v_sz_boxed_3792_; size_t v_i_boxed_3793_; lean_object* v_res_3794_; 
v_post_boxed_3791_ = lean_unbox(v_post_3777_);
v_sz_boxed_3792_ = lean_unbox_usize(v_sz_3780_);
lean_dec(v_sz_3780_);
v_i_boxed_3793_ = lean_unbox_usize(v_i_3781_);
lean_dec(v_i_3781_);
v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(v_erased_3776_, v_post_boxed_3791_, v___x_3778_, v_as_3779_, v_sz_boxed_3792_, v_i_boxed_3793_, v_b_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v_as_3779_);
lean_dec(v___x_3778_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t v_post_3797_, lean_object* v_s_3798_, lean_object* v_erased_3799_, lean_object* v_e_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v___y_3813_; lean_object* v_a_3835_; lean_object* v_indexConfig_3879_; lean_object* v_config_3880_; uint8_t v_trackZetaDelta_3881_; lean_object* v_zetaDeltaSet_3882_; lean_object* v_lctx_3883_; lean_object* v_localInstances_3884_; lean_object* v_defEqCtx_x3f_3885_; lean_object* v_synthPendingDepth_3886_; lean_object* v_canUnfold_x3f_3887_; uint8_t v_univApprox_3888_; uint8_t v_inTypeClassResolution_3889_; uint8_t v_cacheInferType_3890_; uint64_t v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_indexConfig_3879_ = lean_ctor_get(v_a_3802_, 4);
v_config_3880_ = lean_ctor_get(v_indexConfig_3879_, 0);
v_trackZetaDelta_3881_ = lean_ctor_get_uint8(v_a_3804_, sizeof(void*)*7);
v_zetaDeltaSet_3882_ = lean_ctor_get(v_a_3804_, 1);
v_lctx_3883_ = lean_ctor_get(v_a_3804_, 2);
v_localInstances_3884_ = lean_ctor_get(v_a_3804_, 3);
v_defEqCtx_x3f_3885_ = lean_ctor_get(v_a_3804_, 4);
v_synthPendingDepth_3886_ = lean_ctor_get(v_a_3804_, 5);
v_canUnfold_x3f_3887_ = lean_ctor_get(v_a_3804_, 6);
v_univApprox_3888_ = lean_ctor_get_uint8(v_a_3804_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3889_ = lean_ctor_get_uint8(v_a_3804_, sizeof(void*)*7 + 2);
v_cacheInferType_3890_ = lean_ctor_get_uint8(v_a_3804_, sizeof(void*)*7 + 3);
v___x_3891_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3880_);
lean_inc_ref(v_config_3880_);
v___x_3892_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3892_, 0, v_config_3880_);
lean_ctor_set_uint64(v___x_3892_, sizeof(void*)*1, v___x_3891_);
lean_inc(v_canUnfold_x3f_3887_);
lean_inc(v_synthPendingDepth_3886_);
lean_inc(v_defEqCtx_x3f_3885_);
lean_inc_ref(v_localInstances_3884_);
lean_inc_ref(v_lctx_3883_);
lean_inc(v_zetaDeltaSet_3882_);
v___x_3893_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v_zetaDeltaSet_3882_);
lean_ctor_set(v___x_3893_, 2, v_lctx_3883_);
lean_ctor_set(v___x_3893_, 3, v_localInstances_3884_);
lean_ctor_set(v___x_3893_, 4, v_defEqCtx_x3f_3885_);
lean_ctor_set(v___x_3893_, 5, v_synthPendingDepth_3886_);
lean_ctor_set(v___x_3893_, 6, v_canUnfold_x3f_3887_);
lean_ctor_set_uint8(v___x_3893_, sizeof(void*)*7, v_trackZetaDelta_3881_);
lean_ctor_set_uint8(v___x_3893_, sizeof(void*)*7 + 1, v_univApprox_3888_);
lean_ctor_set_uint8(v___x_3893_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3889_);
lean_ctor_set_uint8(v___x_3893_, sizeof(void*)*7 + 3, v_cacheInferType_3890_);
lean_inc_ref(v_e_3800_);
v___x_3894_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_s_3798_, v_e_3800_, v___x_3893_, v_a_3805_, v_a_3806_, v_a_3807_);
lean_dec_ref(v___x_3893_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref(v___x_3894_);
v_a_3835_ = v_a_3895_;
goto v___jp_3834_;
}
else
{
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3896_; 
v_a_3896_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3896_);
lean_dec_ref(v___x_3894_);
v_a_3835_ = v_a_3896_;
goto v___jp_3834_;
}
else
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec_ref(v_e_3800_);
lean_dec_ref(v_erased_3799_);
v_a_3897_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3894_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3894_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
v___jp_3809_:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
return v___x_3811_;
}
v___jp_3812_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v_a_3816_; uint8_t v___x_3817_; 
v___x_3814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3815_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3814_, v_a_3806_);
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref(v___x_3815_);
v___x_3817_ = lean_unbox(v_a_3816_);
lean_dec(v_a_3816_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v___y_3813_);
lean_dec_ref(v_e_3800_);
goto v___jp_3809_;
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3818_ = lean_obj_once(&l_Lean_Meta_Simp_simprocCore___closed__2, &l_Lean_Meta_Simp_simprocCore___closed__2_once, _init_l_Lean_Meta_Simp_simprocCore___closed__2);
v___x_3819_ = l_Lean_stringToMessageData(v___y_3813_);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_obj_once(&l_Lean_Meta_Simp_simprocCore___closed__4, &l_Lean_Meta_Simp_simprocCore___closed__4_once, _init_l_Lean_Meta_Simp_simprocCore___closed__4);
v___x_3822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = l_Lean_MessageData_ofExpr(v_e_3800_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3814_, v___x_3824_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_dec_ref(v___x_3825_);
goto v___jp_3809_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3825_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3825_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
v___jp_3834_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3836_ = lean_array_get_size(v_a_3835_);
v___x_3837_ = lean_unsigned_to_nat(0u);
v___x_3838_ = lean_nat_dec_eq(v___x_3836_, v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; size_t v_sz_3843_; size_t v___x_3844_; lean_object* v___x_3845_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_box(v___x_3838_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v_e_3800_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3839_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v_sz_3843_ = lean_array_size(v_a_3835_);
v___x_3844_ = ((size_t)0ULL);
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(v_erased_3799_, v_post_3797_, v___x_3836_, v_a_3835_, v_sz_3843_, v___x_3844_, v___x_3842_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
lean_dec_ref(v_a_3835_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3868_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3848_ = v___x_3845_;
v_isShared_3849_ = v_isSharedCheck_3868_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3845_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3868_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v_fst_3850_; 
v_fst_3850_ = lean_ctor_get(v_a_3846_, 0);
if (lean_obj_tag(v_fst_3850_) == 0)
{
lean_object* v_snd_3851_; lean_object* v_snd_3852_; uint8_t v___x_3853_; 
v_snd_3851_ = lean_ctor_get(v_a_3846_, 1);
lean_inc(v_snd_3851_);
lean_dec(v_a_3846_);
v_snd_3852_ = lean_ctor_get(v_snd_3851_, 1);
v___x_3853_ = lean_unbox(v_snd_3852_);
if (v___x_3853_ == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3856_; 
lean_dec(v_snd_3851_);
v___x_3854_ = ((lean_object*)(l_Lean_Meta_Simp_dsimprocCore___closed__0));
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v___x_3854_);
v___x_3856_ = v___x_3848_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
else
{
lean_object* v_fst_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
v_fst_3858_ = lean_ctor_get(v_snd_3851_, 0);
lean_inc(v_fst_3858_);
lean_dec(v_snd_3851_);
v___x_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3859_, 0, v_fst_3858_);
v___x_3860_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v___x_3860_);
v___x_3862_ = v___x_3848_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
else
{
lean_object* v_val_3864_; lean_object* v___x_3866_; 
lean_inc_ref(v_fst_3850_);
lean_dec(v_a_3846_);
v_val_3864_ = lean_ctor_get(v_fst_3850_, 0);
lean_inc(v_val_3864_);
lean_dec_ref(v_fst_3850_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 0, v_val_3864_);
v___x_3866_ = v___x_3848_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_val_3864_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
v_a_3869_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3845_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3845_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
else
{
lean_dec_ref(v_a_3835_);
lean_dec_ref(v_erased_3799_);
if (v_post_3797_ == 0)
{
lean_object* v___x_3877_; 
v___x_3877_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__6));
v___y_3813_ = v___x_3877_;
goto v___jp_3812_;
}
else
{
lean_object* v___x_3878_; 
v___x_3878_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__7));
v___y_3813_ = v___x_3878_;
goto v___jp_3812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object* v_post_3905_, lean_object* v_s_3906_, lean_object* v_erased_3907_, lean_object* v_e_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
uint8_t v_post_boxed_3917_; lean_object* v_res_3918_; 
v_post_boxed_3917_ = lean_unbox(v_post_3905_);
v_res_3918_ = l_Lean_Meta_Simp_dsimprocCore(v_post_boxed_3917_, v_s_3906_, v_erased_3907_, v_e_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_);
lean_dec(v_a_3915_);
lean_dec_ref(v_a_3914_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object* v_ss_3919_, lean_object* v_declName_3920_, uint8_t v_post_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3925_ = lean_array_get_size(v_ss_3919_);
v___x_3926_ = lean_unsigned_to_nat(0u);
v___x_3927_ = lean_nat_dec_eq(v___x_3925_, v___x_3926_);
if (v___x_3927_ == 0)
{
uint8_t v___x_3928_; 
v___x_3928_ = lean_nat_dec_lt(v___x_3926_, v___x_3925_);
if (v___x_3928_ == 0)
{
lean_object* v___x_3929_; 
lean_dec(v_declName_3920_);
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_ss_3919_);
return v___x_3929_;
}
else
{
lean_object* v_v_3930_; lean_object* v___x_3931_; 
v_v_3930_ = lean_array_fget_borrowed(v_ss_3919_, v___x_3926_);
lean_inc(v_v_3930_);
v___x_3931_ = l_Lean_Meta_Simp_Simprocs_add(v_v_3930_, v_declName_3920_, v_post_3921_, v_a_3922_, v_a_3923_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3942_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3934_ = v___x_3931_;
v_isShared_3935_ = v_isSharedCheck_3942_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3931_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3942_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; lean_object* v_xs_x27_3937_; lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3936_ = lean_box(0);
v_xs_x27_3937_ = lean_array_fset(v_ss_3919_, v___x_3926_, v___x_3936_);
v___x_3938_ = lean_array_fset(v_xs_x27_3937_, v___x_3926_, v_a_3932_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 0, v___x_3938_);
v___x_3940_ = v___x_3934_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v_ss_3919_);
v_a_3943_ = lean_ctor_get(v___x_3931_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3931_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3931_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
}
else
{
lean_object* v_s_3951_; lean_object* v___x_3952_; 
lean_dec_ref(v_ss_3919_);
v_s_3951_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_3952_ = l_Lean_Meta_Simp_Simprocs_add(v_s_3951_, v_declName_3920_, v_post_3921_, v_a_3922_, v_a_3923_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_3963_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3955_ = v___x_3952_;
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_a_3953_);
lean_dec(v___x_3952_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_3963_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3957_ = lean_unsigned_to_nat(1u);
v___x_3958_ = lean_mk_empty_array_with_capacity(v___x_3957_);
v___x_3959_ = lean_array_push(v___x_3958_, v_a_3953_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 0, v___x_3959_);
v___x_3961_ = v___x_3955_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
v_a_3964_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3952_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3952_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object* v_ss_3972_, lean_object* v_declName_3973_, lean_object* v_post_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_){
_start:
{
uint8_t v_post_boxed_3978_; lean_object* v_res_3979_; 
v_post_boxed_3978_ = lean_unbox(v_post_3974_);
v_res_3979_ = l_Lean_Meta_Simp_SimprocsArray_add(v_ss_3972_, v_declName_3973_, v_post_boxed_3978_, v_a_3975_, v_a_3976_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(lean_object* v_declName_3980_, size_t v_sz_3981_, size_t v_i_3982_, lean_object* v_bs_3983_){
_start:
{
uint8_t v___x_3984_; 
v___x_3984_ = lean_usize_dec_lt(v_i_3982_, v_sz_3981_);
if (v___x_3984_ == 0)
{
lean_dec(v_declName_3980_);
return v_bs_3983_;
}
else
{
lean_object* v_v_3985_; lean_object* v___x_3986_; lean_object* v_bs_x27_3987_; lean_object* v___x_3988_; size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v_v_3985_ = lean_array_uget(v_bs_3983_, v_i_3982_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v_bs_x27_3987_ = lean_array_uset(v_bs_3983_, v_i_3982_, v___x_3986_);
lean_inc(v_declName_3980_);
v___x_3988_ = l_Lean_Meta_Simp_Simprocs_erase(v_v_3985_, v_declName_3980_);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_add(v_i_3982_, v___x_3989_);
v___x_3991_ = lean_array_uset(v_bs_x27_3987_, v_i_3982_, v___x_3988_);
v_i_3982_ = v___x_3990_;
v_bs_3983_ = v___x_3991_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0___boxed(lean_object* v_declName_3993_, lean_object* v_sz_3994_, lean_object* v_i_3995_, lean_object* v_bs_3996_){
_start:
{
size_t v_sz_boxed_3997_; size_t v_i_boxed_3998_; lean_object* v_res_3999_; 
v_sz_boxed_3997_ = lean_unbox_usize(v_sz_3994_);
lean_dec(v_sz_3994_);
v_i_boxed_3998_ = lean_unbox_usize(v_i_3995_);
lean_dec(v_i_3995_);
v_res_3999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(v_declName_3993_, v_sz_boxed_3997_, v_i_boxed_3998_, v_bs_3996_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object* v_ss_4000_, lean_object* v_declName_4001_){
_start:
{
size_t v_sz_4002_; size_t v___x_4003_; lean_object* v___x_4004_; 
v_sz_4002_ = lean_array_size(v_ss_4000_);
v___x_4003_ = ((size_t)0ULL);
v___x_4004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(v_declName_4001_, v_sz_4002_, v___x_4003_, v_ss_4000_);
return v___x_4004_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(lean_object* v_declName_4005_, lean_object* v_as_4006_, size_t v_i_4007_, size_t v_stop_4008_){
_start:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_usize_dec_eq(v_i_4007_, v_stop_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v_erased_4011_; uint8_t v___x_4012_; 
v___x_4010_ = lean_array_uget_borrowed(v_as_4006_, v_i_4007_);
v_erased_4011_ = lean_ctor_get(v___x_4010_, 3);
lean_inc_ref(v_erased_4011_);
v___x_4012_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_erased_4011_, v_declName_4005_);
if (v___x_4012_ == 0)
{
size_t v___x_4013_; size_t v___x_4014_; 
v___x_4013_ = ((size_t)1ULL);
v___x_4014_ = lean_usize_add(v_i_4007_, v___x_4013_);
v_i_4007_ = v___x_4014_;
goto _start;
}
else
{
return v___x_4012_;
}
}
else
{
uint8_t v___x_4016_; 
v___x_4016_ = 0;
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0___boxed(lean_object* v_declName_4017_, lean_object* v_as_4018_, lean_object* v_i_4019_, lean_object* v_stop_4020_){
_start:
{
size_t v_i_boxed_4021_; size_t v_stop_boxed_4022_; uint8_t v_res_4023_; lean_object* v_r_4024_; 
v_i_boxed_4021_ = lean_unbox_usize(v_i_4019_);
lean_dec(v_i_4019_);
v_stop_boxed_4022_ = lean_unbox_usize(v_stop_4020_);
lean_dec(v_stop_4020_);
v_res_4023_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(v_declName_4017_, v_as_4018_, v_i_boxed_4021_, v_stop_boxed_4022_);
lean_dec_ref(v_as_4018_);
lean_dec(v_declName_4017_);
v_r_4024_ = lean_box(v_res_4023_);
return v_r_4024_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object* v_ss_4025_, lean_object* v_declName_4026_){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = lean_array_get_size(v_ss_4025_);
v___x_4029_ = lean_nat_dec_lt(v___x_4027_, v___x_4028_);
if (v___x_4029_ == 0)
{
return v___x_4029_;
}
else
{
if (v___x_4029_ == 0)
{
return v___x_4029_;
}
else
{
size_t v___x_4030_; size_t v___x_4031_; uint8_t v___x_4032_; 
v___x_4030_ = ((size_t)0ULL);
v___x_4031_ = lean_usize_of_nat(v___x_4028_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(v_declName_4026_, v_ss_4025_, v___x_4030_, v___x_4031_);
return v___x_4032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object* v_ss_4033_, lean_object* v_declName_4034_){
_start:
{
uint8_t v_res_4035_; lean_object* v_r_4036_; 
v_res_4035_ = l_Lean_Meta_Simp_SimprocsArray_isErased(v_ss_4033_, v_declName_4034_);
lean_dec(v_declName_4034_);
lean_dec_ref(v_ss_4033_);
v_r_4036_ = lean_box(v_res_4035_);
return v_r_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(uint8_t v_post_4037_, lean_object* v_as_4038_, size_t v_sz_4039_, size_t v_i_4040_, lean_object* v_b_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_a_4051_; uint8_t v_cache_4055_; 
v_cache_4055_ = lean_usize_dec_lt(v_i_4040_, v_sz_4039_);
if (v_cache_4055_ == 0)
{
lean_object* v___x_4056_; 
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v_b_4041_);
return v___x_4056_;
}
else
{
lean_object* v_snd_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4200_; 
v_snd_4057_ = lean_ctor_get(v_b_4041_, 1);
v_isSharedCheck_4200_ = !lean_is_exclusive(v_b_4041_);
if (v_isSharedCheck_4200_ == 0)
{
lean_object* v_unused_4201_; 
v_unused_4201_ = lean_ctor_get(v_b_4041_, 0);
lean_dec(v_unused_4201_);
v___x_4059_ = v_b_4041_;
v_isShared_4060_ = v_isSharedCheck_4200_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_snd_4057_);
lean_dec(v_b_4041_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4200_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v_snd_4061_; lean_object* v_snd_4062_; lean_object* v_fst_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4198_; 
v_snd_4061_ = lean_ctor_get(v_snd_4057_, 1);
lean_inc(v_snd_4061_);
v_snd_4062_ = lean_ctor_get(v_snd_4061_, 1);
lean_inc(v_snd_4062_);
v_fst_4063_ = lean_ctor_get(v_snd_4057_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v_snd_4057_);
if (v_isSharedCheck_4198_ == 0)
{
lean_object* v_unused_4199_; 
v_unused_4199_ = lean_ctor_get(v_snd_4057_, 1);
lean_dec(v_unused_4199_);
v___x_4065_ = v_snd_4057_;
v_isShared_4066_ = v_isSharedCheck_4198_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_fst_4063_);
lean_dec(v_snd_4057_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4198_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v_fst_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4196_; 
v_fst_4067_ = lean_ctor_get(v_snd_4061_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_snd_4061_);
if (v_isSharedCheck_4196_ == 0)
{
lean_object* v_unused_4197_; 
v_unused_4197_ = lean_ctor_get(v_snd_4061_, 1);
lean_dec(v_unused_4197_);
v___x_4069_ = v_snd_4061_;
v_isShared_4070_ = v_isSharedCheck_4196_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_fst_4067_);
lean_dec(v_snd_4061_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4196_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v_fst_4071_; lean_object* v_snd_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4195_; 
v_fst_4071_ = lean_ctor_get(v_snd_4062_, 0);
v_snd_4072_ = lean_ctor_get(v_snd_4062_, 1);
v_isSharedCheck_4195_ = !lean_is_exclusive(v_snd_4062_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4074_ = v_snd_4062_;
v_isShared_4075_ = v_isSharedCheck_4195_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_snd_4072_);
lean_inc(v_fst_4071_);
lean_dec(v_snd_4062_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4195_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4080_; uint8_t v_found_4095_; lean_object* v_a_4096_; lean_object* v___y_4098_; 
v___x_4076_ = lean_box(0);
v_found_4095_ = 0;
v_a_4096_ = lean_array_uget_borrowed(v_as_4038_, v_i_4040_);
if (v_post_4037_ == 0)
{
lean_object* v_pre_4193_; 
v_pre_4193_ = lean_ctor_get(v_a_4096_, 0);
lean_inc_ref(v_pre_4193_);
v___y_4098_ = v_pre_4193_;
goto v___jp_4097_;
}
else
{
lean_object* v_post_4194_; 
v_post_4194_ = lean_ctor_get(v_a_4096_, 1);
lean_inc_ref(v_post_4194_);
v___y_4098_ = v_post_4194_;
goto v___jp_4097_;
}
v___jp_4077_:
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_box(v___y_4080_);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 1, v___x_4081_);
lean_ctor_set(v___x_4074_, 0, v___y_4079_);
v___x_4083_ = v___x_4074_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___y_4079_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4085_; 
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v___x_4083_);
lean_ctor_set(v___x_4069_, 0, v___y_4078_);
v___x_4085_ = v___x_4069_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___y_4078_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4083_);
v___x_4085_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4086_ = lean_box(v_cache_4055_);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 1, v___x_4085_);
lean_ctor_set(v___x_4065_, 0, v___x_4086_);
v___x_4088_ = v___x_4065_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4086_);
lean_ctor_set(v_reuseFailAlloc_4092_, 1, v___x_4085_);
v___x_4088_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
lean_object* v___x_4090_; 
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 1, v___x_4088_);
lean_ctor_set(v___x_4059_, 0, v___x_4076_);
v___x_4090_ = v___x_4059_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
v_a_4051_ = v___x_4090_;
goto v___jp_4050_;
}
}
}
}
}
v___jp_4097_:
{
lean_object* v_erased_4099_; lean_object* v___x_4100_; 
v_erased_4099_ = lean_ctor_get(v_a_4096_, 3);
lean_inc(v_fst_4067_);
lean_inc_ref(v_erased_4099_);
v___x_4100_ = l_Lean_Meta_Simp_simprocCore(v_post_4037_, v___y_4098_, v_erased_4099_, v_fst_4067_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref(v___x_4100_);
switch(lean_obj_tag(v_a_4101_))
{
case 0:
{
lean_object* v_r_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4132_; 
lean_del_object(v___x_4074_);
lean_del_object(v___x_4069_);
lean_del_object(v___x_4065_);
lean_del_object(v___x_4059_);
v_r_4102_ = lean_ctor_get(v_a_4101_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v_a_4101_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4104_ = v_a_4101_;
v_isShared_4105_ = v_isSharedCheck_4132_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_r_4102_);
lean_dec(v_a_4101_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4132_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
uint8_t v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_unbox(v_snd_4072_);
lean_inc(v_fst_4071_);
v___x_4107_ = l_Lean_Meta_Simp_mkEqTransOptProofResult(v_fst_4071_, v___x_4106_, v_r_4102_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4123_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4123_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4123_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v_a_4108_);
v___x_4113_ = v___x_4104_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4120_; 
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4115_, 0, v_fst_4071_);
lean_ctor_set(v___x_4115_, 1, v_snd_4072_);
v___x_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4116_, 0, v_fst_4067_);
lean_ctor_set(v___x_4116_, 1, v___x_4115_);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v_fst_4063_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4114_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v___x_4118_);
v___x_4120_ = v___x_4110_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_del_object(v___x_4104_);
lean_dec(v_snd_4072_);
lean_dec(v_fst_4071_);
lean_dec(v_fst_4067_);
lean_dec(v_fst_4063_);
v_a_4124_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4107_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4107_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
case 1:
{
lean_object* v_e_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4163_; 
lean_del_object(v___x_4074_);
lean_del_object(v___x_4069_);
lean_del_object(v___x_4065_);
lean_del_object(v___x_4059_);
v_e_4133_ = lean_ctor_get(v_a_4101_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v_a_4101_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4135_ = v_a_4101_;
v_isShared_4136_ = v_isSharedCheck_4163_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_e_4133_);
lean_dec(v_a_4101_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4163_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
uint8_t v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_unbox(v_snd_4072_);
lean_inc(v_fst_4071_);
v___x_4138_ = l_Lean_Meta_Simp_mkEqTransOptProofResult(v_fst_4071_, v___x_4137_, v_e_4133_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4154_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4154_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4154_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v_a_4139_);
v___x_4144_ = v___x_4135_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4151_; 
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
v___x_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4146_, 0, v_fst_4071_);
lean_ctor_set(v___x_4146_, 1, v_snd_4072_);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v_fst_4067_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v_fst_4063_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4145_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4149_);
v___x_4151_ = v___x_4141_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_del_object(v___x_4135_);
lean_dec(v_snd_4072_);
lean_dec(v_fst_4071_);
lean_dec(v_fst_4067_);
lean_dec(v_fst_4063_);
v_a_4155_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4138_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4138_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
default: 
{
lean_object* v_e_x3f_4164_; 
v_e_x3f_4164_ = lean_ctor_get(v_a_4101_, 0);
lean_inc(v_e_x3f_4164_);
lean_dec_ref(v_a_4101_);
if (lean_obj_tag(v_e_x3f_4164_) == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_del_object(v___x_4074_);
lean_del_object(v___x_4069_);
lean_del_object(v___x_4065_);
lean_del_object(v___x_4059_);
v___x_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4165_, 0, v_fst_4071_);
lean_ctor_set(v___x_4165_, 1, v_snd_4072_);
v___x_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4166_, 0, v_fst_4067_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4167_, 0, v_fst_4063_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4076_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v_a_4051_ = v___x_4168_;
goto v___jp_4050_;
}
else
{
lean_object* v_val_4169_; lean_object* v_expr_4170_; lean_object* v_proof_x3f_4171_; uint8_t v_cache_4172_; lean_object* v___x_4173_; 
lean_dec(v_fst_4067_);
lean_dec(v_fst_4063_);
v_val_4169_ = lean_ctor_get(v_e_x3f_4164_, 0);
lean_inc(v_val_4169_);
lean_dec_ref(v_e_x3f_4164_);
v_expr_4170_ = lean_ctor_get(v_val_4169_, 0);
lean_inc_ref(v_expr_4170_);
v_proof_x3f_4171_ = lean_ctor_get(v_val_4169_, 1);
lean_inc(v_proof_x3f_4171_);
v_cache_4172_ = lean_ctor_get_uint8(v_val_4169_, sizeof(void*)*2);
lean_dec(v_val_4169_);
v___x_4173_ = l_Lean_Meta_mkEqTrans_x3f(v_fst_4071_, v_proof_x3f_4171_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4173_) == 0)
{
uint8_t v___x_4174_; 
v___x_4174_ = lean_unbox(v_snd_4072_);
lean_dec(v_snd_4072_);
if (v___x_4174_ == 0)
{
lean_object* v_a_4175_; 
v_a_4175_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4173_);
v___y_4078_ = v_expr_4170_;
v___y_4079_ = v_a_4175_;
v___y_4080_ = v_found_4095_;
goto v___jp_4077_;
}
else
{
lean_object* v_a_4176_; 
v_a_4176_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4173_);
v___y_4078_ = v_expr_4170_;
v___y_4079_ = v_a_4176_;
v___y_4080_ = v_cache_4172_;
goto v___jp_4077_;
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec_ref(v_expr_4170_);
lean_del_object(v___x_4074_);
lean_dec(v_snd_4072_);
lean_del_object(v___x_4069_);
lean_del_object(v___x_4065_);
lean_del_object(v___x_4059_);
v_a_4177_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4173_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4173_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_del_object(v___x_4074_);
lean_dec(v_snd_4072_);
lean_dec(v_fst_4071_);
lean_del_object(v___x_4069_);
lean_dec(v_fst_4067_);
lean_del_object(v___x_4065_);
lean_dec(v_fst_4063_);
lean_del_object(v___x_4059_);
v_a_4185_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4100_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4100_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
}
}
}
}
v___jp_4050_:
{
size_t v___x_4052_; size_t v___x_4053_; 
v___x_4052_ = ((size_t)1ULL);
v___x_4053_ = lean_usize_add(v_i_4040_, v___x_4052_);
v_i_4040_ = v___x_4053_;
v_b_4041_ = v_a_4051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0___boxed(lean_object* v_post_4202_, lean_object* v_as_4203_, lean_object* v_sz_4204_, lean_object* v_i_4205_, lean_object* v_b_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
uint8_t v_post_boxed_4215_; size_t v_sz_boxed_4216_; size_t v_i_boxed_4217_; lean_object* v_res_4218_; 
v_post_boxed_4215_ = lean_unbox(v_post_4202_);
v_sz_boxed_4216_ = lean_unbox_usize(v_sz_4204_);
lean_dec(v_sz_4204_);
v_i_boxed_4217_ = lean_unbox_usize(v_i_4205_);
lean_dec(v_i_4205_);
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(v_post_boxed_4215_, v_as_4203_, v_sz_boxed_4216_, v_i_boxed_4217_, v_b_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v_as_4203_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t v_post_4223_, lean_object* v_ss_4224_, lean_object* v_e_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
uint8_t v_found_4234_; lean_object* v_proof_x3f_4235_; uint8_t v_cache_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; size_t v_sz_4242_; size_t v___x_4243_; lean_object* v___x_4244_; 
v_found_4234_ = 0;
v_proof_x3f_4235_ = lean_box(0);
v_cache_4236_ = 1;
v___x_4237_ = ((lean_object*)(l_Lean_Meta_Simp_simprocArrayCore___closed__0));
v___x_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4238_, 0, v_e_4225_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = lean_box(v_found_4234_);
v___x_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
lean_ctor_set(v___x_4240_, 1, v___x_4238_);
v___x_4241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4241_, 0, v_proof_x3f_4235_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v_sz_4242_ = lean_array_size(v_ss_4224_);
v___x_4243_ = ((size_t)0ULL);
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(v_post_4223_, v_ss_4224_, v_sz_4242_, v___x_4243_, v___x_4241_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4271_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4271_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4271_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v_fst_4249_; 
v_fst_4249_ = lean_ctor_get(v_a_4245_, 0);
if (lean_obj_tag(v_fst_4249_) == 0)
{
lean_object* v_snd_4250_; lean_object* v_fst_4251_; uint8_t v___x_4252_; 
v_snd_4250_ = lean_ctor_get(v_a_4245_, 1);
lean_inc(v_snd_4250_);
lean_dec(v_a_4245_);
v_fst_4251_ = lean_ctor_get(v_snd_4250_, 0);
v___x_4252_ = lean_unbox(v_fst_4251_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4255_; 
lean_dec(v_snd_4250_);
v___x_4253_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__5));
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v___x_4253_);
v___x_4255_ = v___x_4247_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4253_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
else
{
lean_object* v_snd_4257_; lean_object* v_snd_4258_; lean_object* v_fst_4259_; lean_object* v_fst_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4265_; 
v_snd_4257_ = lean_ctor_get(v_snd_4250_, 1);
lean_inc(v_snd_4257_);
lean_dec(v_snd_4250_);
v_snd_4258_ = lean_ctor_get(v_snd_4257_, 1);
lean_inc(v_snd_4258_);
v_fst_4259_ = lean_ctor_get(v_snd_4257_, 0);
lean_inc(v_fst_4259_);
lean_dec(v_snd_4257_);
v_fst_4260_ = lean_ctor_get(v_snd_4258_, 0);
lean_inc(v_fst_4260_);
lean_dec(v_snd_4258_);
v___x_4261_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4261_, 0, v_fst_4259_);
lean_ctor_set(v___x_4261_, 1, v_fst_4260_);
lean_ctor_set_uint8(v___x_4261_, sizeof(void*)*2, v_cache_4236_);
v___x_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
v___x_4263_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v___x_4263_);
v___x_4265_ = v___x_4247_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
else
{
lean_object* v_val_4267_; lean_object* v___x_4269_; 
lean_inc_ref(v_fst_4249_);
lean_dec(v_a_4245_);
v_val_4267_ = lean_ctor_get(v_fst_4249_, 0);
lean_inc(v_val_4267_);
lean_dec_ref(v_fst_4249_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v_val_4267_);
v___x_4269_ = v___x_4247_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_val_4267_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_a_4272_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4244_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4244_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object* v_post_4280_, lean_object* v_ss_4281_, lean_object* v_e_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_){
_start:
{
uint8_t v_post_boxed_4291_; lean_object* v_res_4292_; 
v_post_boxed_4291_ = lean_unbox(v_post_4280_);
v_res_4292_ = l_Lean_Meta_Simp_simprocArrayCore(v_post_boxed_4291_, v_ss_4281_, v_e_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
lean_dec(v_a_4283_);
lean_dec_ref(v_ss_4281_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(uint8_t v_post_4293_, lean_object* v_as_4294_, size_t v_sz_4295_, size_t v_i_4296_, lean_object* v_b_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_a_4307_; uint8_t v___x_4311_; 
v___x_4311_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; 
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v_b_4297_);
return v___x_4312_;
}
else
{
lean_object* v_snd_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4369_; 
v_snd_4313_ = lean_ctor_get(v_b_4297_, 1);
v_isSharedCheck_4369_ = !lean_is_exclusive(v_b_4297_);
if (v_isSharedCheck_4369_ == 0)
{
lean_object* v_unused_4370_; 
v_unused_4370_ = lean_ctor_get(v_b_4297_, 0);
lean_dec(v_unused_4370_);
v___x_4315_ = v_b_4297_;
v_isShared_4316_ = v_isSharedCheck_4369_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_snd_4313_);
lean_dec(v_b_4297_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4369_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v_fst_4317_; lean_object* v_snd_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4368_; 
v_fst_4317_ = lean_ctor_get(v_snd_4313_, 0);
v_snd_4318_ = lean_ctor_get(v_snd_4313_, 1);
v_isSharedCheck_4368_ = !lean_is_exclusive(v_snd_4313_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4320_ = v_snd_4313_;
v_isShared_4321_ = v_isSharedCheck_4368_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_snd_4318_);
lean_inc(v_fst_4317_);
lean_dec(v_snd_4313_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4368_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4322_; lean_object* v_a_4323_; lean_object* v___y_4325_; 
v___x_4322_ = lean_box(0);
v_a_4323_ = lean_array_uget_borrowed(v_as_4294_, v_i_4296_);
if (v_post_4293_ == 0)
{
lean_object* v_pre_4366_; 
v_pre_4366_ = lean_ctor_get(v_a_4323_, 0);
lean_inc_ref(v_pre_4366_);
v___y_4325_ = v_pre_4366_;
goto v___jp_4324_;
}
else
{
lean_object* v_post_4367_; 
v_post_4367_ = lean_ctor_get(v_a_4323_, 1);
lean_inc_ref(v_post_4367_);
v___y_4325_ = v_post_4367_;
goto v___jp_4324_;
}
v___jp_4324_:
{
lean_object* v_erased_4326_; lean_object* v___x_4327_; 
v_erased_4326_ = lean_ctor_get(v_a_4323_, 3);
lean_inc(v_snd_4318_);
lean_inc_ref(v_erased_4326_);
v___x_4327_ = l_Lean_Meta_Simp_dsimprocCore(v_post_4293_, v___y_4325_, v_erased_4326_, v_snd_4318_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4357_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4357_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4357_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4357_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
if (lean_obj_tag(v_a_4328_) == 2)
{
lean_object* v_e_x3f_4332_; 
lean_del_object(v___x_4330_);
v_e_x3f_4332_ = lean_ctor_get(v_a_4328_, 0);
lean_inc(v_e_x3f_4332_);
lean_dec_ref(v_a_4328_);
if (lean_obj_tag(v_e_x3f_4332_) == 0)
{
lean_object* v___x_4334_; 
if (v_isShared_4321_ == 0)
{
v___x_4334_ = v___x_4320_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_fst_4317_);
lean_ctor_set(v_reuseFailAlloc_4338_, 1, v_snd_4318_);
v___x_4334_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4336_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 1, v___x_4334_);
lean_ctor_set(v___x_4315_, 0, v___x_4322_);
v___x_4336_ = v___x_4315_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4322_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
v_a_4307_ = v___x_4336_;
goto v___jp_4306_;
}
}
}
else
{
lean_object* v_val_4339_; lean_object* v___x_4340_; lean_object* v___x_4342_; 
lean_dec(v_snd_4318_);
lean_dec(v_fst_4317_);
v_val_4339_ = lean_ctor_get(v_e_x3f_4332_, 0);
lean_inc(v_val_4339_);
lean_dec_ref(v_e_x3f_4332_);
v___x_4340_ = lean_box(v___x_4311_);
if (v_isShared_4321_ == 0)
{
lean_ctor_set(v___x_4320_, 1, v_val_4339_);
lean_ctor_set(v___x_4320_, 0, v___x_4340_);
v___x_4342_ = v___x_4320_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4346_, 1, v_val_4339_);
v___x_4342_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4344_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 1, v___x_4342_);
lean_ctor_set(v___x_4315_, 0, v___x_4322_);
v___x_4344_ = v___x_4315_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4322_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v___x_4342_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
v_a_4307_ = v___x_4344_;
goto v___jp_4306_;
}
}
}
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4349_; 
v___x_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4347_, 0, v_a_4328_);
if (v_isShared_4321_ == 0)
{
v___x_4349_ = v___x_4320_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_fst_4317_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_snd_4318_);
v___x_4349_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4351_; 
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 1, v___x_4349_);
lean_ctor_set(v___x_4315_, 0, v___x_4347_);
v___x_4351_ = v___x_4315_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4355_, 1, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
lean_object* v___x_4353_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v___x_4351_);
v___x_4353_ = v___x_4330_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4351_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_del_object(v___x_4320_);
lean_dec(v_snd_4318_);
lean_dec(v_fst_4317_);
lean_del_object(v___x_4315_);
v_a_4358_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4327_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4327_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
}
}
}
v___jp_4306_:
{
size_t v___x_4308_; size_t v___x_4309_; 
v___x_4308_ = ((size_t)1ULL);
v___x_4309_ = lean_usize_add(v_i_4296_, v___x_4308_);
v_i_4296_ = v___x_4309_;
v_b_4297_ = v_a_4307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0___boxed(lean_object* v_post_4371_, lean_object* v_as_4372_, lean_object* v_sz_4373_, lean_object* v_i_4374_, lean_object* v_b_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
uint8_t v_post_boxed_4384_; size_t v_sz_boxed_4385_; size_t v_i_boxed_4386_; lean_object* v_res_4387_; 
v_post_boxed_4384_ = lean_unbox(v_post_4371_);
v_sz_boxed_4385_ = lean_unbox_usize(v_sz_4373_);
lean_dec(v_sz_4373_);
v_i_boxed_4386_ = lean_unbox_usize(v_i_4374_);
lean_dec(v_i_4374_);
v_res_4387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(v_post_boxed_4384_, v_as_4372_, v_sz_boxed_4385_, v_i_boxed_4386_, v_b_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec_ref(v_as_4372_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t v_post_4388_, lean_object* v_ss_4389_, lean_object* v_e_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
uint8_t v_found_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; size_t v_sz_4404_; size_t v___x_4405_; lean_object* v___x_4406_; 
v_found_4399_ = 0;
v___x_4400_ = lean_box(0);
v___x_4401_ = lean_box(v_found_4399_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4401_);
lean_ctor_set(v___x_4402_, 1, v_e_4390_);
v___x_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4400_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v_sz_4404_ = lean_array_size(v_ss_4389_);
v___x_4405_ = ((size_t)0ULL);
v___x_4406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(v_post_4388_, v_ss_4389_, v_sz_4404_, v___x_4405_, v___x_4403_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4429_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4429_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4429_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v_fst_4411_; 
v_fst_4411_ = lean_ctor_get(v_a_4407_, 0);
if (lean_obj_tag(v_fst_4411_) == 0)
{
lean_object* v_snd_4412_; lean_object* v_fst_4413_; uint8_t v___x_4414_; 
v_snd_4412_ = lean_ctor_get(v_a_4407_, 1);
lean_inc(v_snd_4412_);
lean_dec(v_a_4407_);
v_fst_4413_ = lean_ctor_get(v_snd_4412_, 0);
v___x_4414_ = lean_unbox(v_fst_4413_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4415_; lean_object* v___x_4417_; 
lean_dec(v_snd_4412_);
v___x_4415_ = ((lean_object*)(l_Lean_Meta_Simp_dsimprocCore___closed__0));
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4415_);
v___x_4417_ = v___x_4409_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4415_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
else
{
lean_object* v_snd_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v_snd_4419_ = lean_ctor_get(v_snd_4412_, 1);
lean_inc(v_snd_4419_);
lean_dec(v_snd_4412_);
v___x_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4420_, 0, v_snd_4419_);
v___x_4421_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v___x_4421_);
v___x_4423_ = v___x_4409_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
else
{
lean_object* v_val_4425_; lean_object* v___x_4427_; 
lean_inc_ref(v_fst_4411_);
lean_dec(v_a_4407_);
v_val_4425_ = lean_ctor_get(v_fst_4411_, 0);
lean_inc(v_val_4425_);
lean_dec_ref(v_fst_4411_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 0, v_val_4425_);
v___x_4427_ = v___x_4409_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_val_4425_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
v_a_4430_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4406_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4406_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object* v_post_4438_, lean_object* v_ss_4439_, lean_object* v_e_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
uint8_t v_post_boxed_4449_; lean_object* v_res_4450_; 
v_post_boxed_4449_ = lean_unbox(v_post_4438_);
v_res_4450_ = l_Lean_Meta_Simp_dsimprocArrayCore(v_post_boxed_4449_, v_ss_4439_, v_e_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_ss_4439_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(lean_object* v_name_4451_, lean_object* v_decl_4452_, lean_object* v_ref_4453_){
_start:
{
lean_object* v_defValue_4455_; lean_object* v_descr_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4483_; 
v_defValue_4455_ = lean_ctor_get(v_decl_4452_, 0);
v_descr_4456_ = lean_ctor_get(v_decl_4452_, 1);
v_isSharedCheck_4483_ = !lean_is_exclusive(v_decl_4452_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4458_ = v_decl_4452_;
v_isShared_4459_ = v_isSharedCheck_4483_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_descr_4456_);
lean_inc(v_defValue_4455_);
lean_dec(v_decl_4452_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4483_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; uint8_t v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4460_ = lean_alloc_ctor(1, 0, 1);
v___x_4461_ = lean_unbox(v_defValue_4455_);
lean_ctor_set_uint8(v___x_4460_, 0, v___x_4461_);
lean_inc(v_name_4451_);
v___x_4462_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4462_, 0, v_name_4451_);
lean_ctor_set(v___x_4462_, 1, v_ref_4453_);
lean_ctor_set(v___x_4462_, 2, v___x_4460_);
lean_ctor_set(v___x_4462_, 3, v_descr_4456_);
lean_inc(v_name_4451_);
v___x_4463_ = lean_register_option(v_name_4451_, v___x_4462_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4473_; 
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4473_ == 0)
{
lean_object* v_unused_4474_; 
v_unused_4474_ = lean_ctor_get(v___x_4463_, 0);
lean_dec(v_unused_4474_);
v___x_4465_ = v___x_4463_;
v_isShared_4466_ = v_isSharedCheck_4473_;
goto v_resetjp_4464_;
}
else
{
lean_dec(v___x_4463_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4473_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
lean_object* v___x_4468_; 
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 1, v_defValue_4455_);
lean_ctor_set(v___x_4458_, 0, v_name_4451_);
v___x_4468_ = v___x_4458_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_name_4451_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_defValue_4455_);
v___x_4468_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
lean_object* v___x_4470_; 
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 0, v___x_4468_);
v___x_4470_ = v___x_4465_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4468_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_del_object(v___x_4458_);
lean_dec(v_defValue_4455_);
lean_dec(v_name_4451_);
v_a_4475_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4463_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4463_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4484_, lean_object* v_decl_4485_, lean_object* v_ref_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(v_name_4484_, v_decl_4485_, v_ref_4486_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4503_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_));
v___x_4504_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_));
v___x_4505_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_));
v___x_4506_ = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(v___x_4503_, v___x_4504_, v___x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4____boxed(lean_object* v_a_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_();
return v_res_4508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(lean_object* v_opts_4509_, lean_object* v_opt_4510_){
_start:
{
lean_object* v_name_4511_; lean_object* v_defValue_4512_; lean_object* v_map_4513_; lean_object* v___x_4514_; 
v_name_4511_ = lean_ctor_get(v_opt_4510_, 0);
v_defValue_4512_ = lean_ctor_get(v_opt_4510_, 1);
v_map_4513_ = lean_ctor_get(v_opts_4509_, 0);
v___x_4514_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4513_, v_name_4511_);
if (lean_obj_tag(v___x_4514_) == 0)
{
uint8_t v___x_4515_; 
v___x_4515_ = lean_unbox(v_defValue_4512_);
return v___x_4515_;
}
else
{
lean_object* v_val_4516_; 
v_val_4516_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_val_4516_);
lean_dec_ref(v___x_4514_);
if (lean_obj_tag(v_val_4516_) == 1)
{
uint8_t v_v_4517_; 
v_v_4517_ = lean_ctor_get_uint8(v_val_4516_, 0);
lean_dec_ref(v_val_4516_);
return v_v_4517_;
}
else
{
uint8_t v___x_4518_; 
lean_dec(v_val_4516_);
v___x_4518_ = lean_unbox(v_defValue_4512_);
return v___x_4518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0___boxed(lean_object* v_opts_4519_, lean_object* v_opt_4520_){
_start:
{
uint8_t v_res_4521_; lean_object* v_r_4522_; 
v_res_4521_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_opts_4519_, v_opt_4520_);
lean_dec_ref(v_opt_4520_);
lean_dec_ref(v_opts_4519_);
v_r_4522_ = lean_box(v_res_4521_);
return v_r_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object* v_s_4523_, lean_object* v_e_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_options_4533_; lean_object* v___x_4534_; uint8_t v___x_4535_; 
v_options_4533_ = lean_ctor_get(v_a_4530_, 2);
v___x_4534_ = l_Lean_Meta_Simp_simprocs;
v___x_4535_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4533_, v___x_4534_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
lean_dec_ref(v_e_4524_);
v___x_4536_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__0));
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
return v___x_4537_;
}
else
{
uint8_t v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = 0;
v___x_4539_ = l_Lean_Meta_Simp_simprocArrayCore(v___x_4538_, v_s_4523_, v_e_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
return v___x_4539_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object* v_s_4540_, lean_object* v_e_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_Meta_Simp_userPreSimprocs(v_s_4540_, v_e_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_s_4540_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object* v_s_4551_, lean_object* v_e_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v_options_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_options_4561_ = lean_ctor_get(v_a_4558_, 2);
v___x_4562_ = l_Lean_Meta_Simp_simprocs;
v___x_4563_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4561_, v___x_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
lean_dec_ref(v_e_4552_);
v___x_4564_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__0));
v___x_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4565_, 0, v___x_4564_);
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; 
v___x_4566_ = l_Lean_Meta_Simp_simprocArrayCore(v___x_4563_, v_s_4551_, v_e_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
return v___x_4566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object* v_s_4567_, lean_object* v_e_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean_Meta_Simp_userPostSimprocs(v_s_4567_, v_e_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_);
lean_dec(v_a_4575_);
lean_dec_ref(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_s_4567_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object* v_s_4578_, lean_object* v_e_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v_options_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v_options_4588_ = lean_ctor_get(v_a_4585_, 2);
v___x_4589_ = l_Lean_Meta_Simp_simprocs;
v___x_4590_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4588_, v___x_4589_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
lean_dec_ref(v_e_4579_);
v___x_4591_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___x_4591_);
return v___x_4592_;
}
else
{
uint8_t v___x_4593_; lean_object* v___x_4594_; 
v___x_4593_ = 0;
v___x_4594_ = l_Lean_Meta_Simp_dsimprocArrayCore(v___x_4593_, v_s_4578_, v_e_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
return v___x_4594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object* v_s_4595_, lean_object* v_e_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_Meta_Simp_userPreDSimprocs(v_s_4595_, v_e_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_s_4595_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object* v_s_4606_, lean_object* v_e_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_){
_start:
{
lean_object* v_options_4616_; lean_object* v___x_4617_; uint8_t v___x_4618_; 
v_options_4616_ = lean_ctor_get(v_a_4613_, 2);
v___x_4617_ = l_Lean_Meta_Simp_simprocs;
v___x_4618_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4616_, v___x_4617_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_dec_ref(v_e_4607_);
v___x_4619_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
v___x_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4619_);
return v___x_4620_;
}
else
{
lean_object* v___x_4621_; 
v___x_4621_ = l_Lean_Meta_Simp_dsimprocArrayCore(v___x_4618_, v_s_4606_, v_e_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_);
return v___x_4621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object* v_s_4622_, lean_object* v_e_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Lean_Meta_Simp_userPostDSimprocs(v_s_4622_, v_e_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec_ref(v_s_4622_);
return v_res_4632_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10(void){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__8));
v___x_4658_ = l_Lean_mkAtom(v___x_4657_);
return v___x_4658_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; 
v___x_4659_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10);
v___x_4660_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4661_ = lean_array_push(v___x_4660_, v___x_4659_);
return v___x_4661_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; 
v___x_4670_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__15));
v___x_4671_ = l_Lean_mkAtom(v___x_4670_);
return v___x_4671_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4672_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16);
v___x_4673_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4674_ = lean_array_push(v___x_4673_, v___x_4672_);
return v___x_4674_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4675_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17);
v___x_4676_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14));
v___x_4677_ = lean_box(2);
v___x_4678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v___x_4676_);
lean_ctor_set(v___x_4678_, 2, v___x_4675_);
return v___x_4678_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4679_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18);
v___x_4680_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11);
v___x_4681_ = lean_array_push(v___x_4680_, v___x_4679_);
return v___x_4681_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4682_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19);
v___x_4683_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9));
v___x_4684_ = lean_box(2);
v___x_4685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4685_, 0, v___x_4684_);
lean_ctor_set(v___x_4685_, 1, v___x_4683_);
lean_ctor_set(v___x_4685_, 2, v___x_4682_);
return v___x_4685_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20);
v___x_4687_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4688_ = lean_array_push(v___x_4687_, v___x_4686_);
return v___x_4688_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4689_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21);
v___x_4690_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__7));
v___x_4691_ = lean_box(2);
v___x_4692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
lean_ctor_set(v___x_4692_, 1, v___x_4690_);
lean_ctor_set(v___x_4692_, 2, v___x_4689_);
return v___x_4692_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4693_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22);
v___x_4694_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4695_ = lean_array_push(v___x_4694_, v___x_4693_);
return v___x_4695_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4696_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23);
v___x_4697_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5));
v___x_4698_ = lean_box(2);
v___x_4699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
lean_ctor_set(v___x_4699_, 1, v___x_4697_);
lean_ctor_set(v___x_4699_, 2, v___x_4696_);
return v___x_4699_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4700_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24);
v___x_4701_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4702_ = lean_array_push(v___x_4701_, v___x_4700_);
return v___x_4702_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4703_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25);
v___x_4704_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2));
v___x_4705_ = lean_box(2);
v___x_4706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4706_, 0, v___x_4705_);
lean_ctor_set(v___x_4706_, 1, v___x_4704_);
lean_ctor_set(v___x_4706_, 2, v___x_4703_);
return v___x_4706_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1(void){
_start:
{
lean_object* v___x_4707_; 
v___x_4707_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0(uint8_t v_x_4708_, lean_object* v___y_4709_){
_start:
{
lean_object* v___x_4710_; 
v___x_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4710_, 0, v___y_4709_);
return v___x_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0___boxed(lean_object* v_x_4711_, lean_object* v___y_4712_){
_start:
{
uint8_t v_x_180__boxed_4713_; lean_object* v_res_4714_; 
v_x_180__boxed_4713_ = lean_unbox(v_x_4711_);
v_res_4714_ = l_Lean_Meta_Simp_mkSimprocExt___lam__0(v_x_180__boxed_4713_, v___y_4712_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1(lean_object* v_s_4715_, lean_object* v_e_4716_){
_start:
{
lean_object* v_toSimprocOLeanEntry_4717_; lean_object* v_proc_4718_; lean_object* v_declName_4719_; uint8_t v_post_4720_; lean_object* v_keys_4721_; lean_object* v___x_4722_; 
v_toSimprocOLeanEntry_4717_ = lean_ctor_get(v_e_4716_, 0);
lean_inc_ref(v_toSimprocOLeanEntry_4717_);
v_proc_4718_ = lean_ctor_get(v_e_4716_, 1);
lean_inc_ref(v_proc_4718_);
lean_dec_ref(v_e_4716_);
v_declName_4719_ = lean_ctor_get(v_toSimprocOLeanEntry_4717_, 0);
lean_inc(v_declName_4719_);
v_post_4720_ = lean_ctor_get_uint8(v_toSimprocOLeanEntry_4717_, sizeof(void*)*2);
v_keys_4721_ = lean_ctor_get(v_toSimprocOLeanEntry_4717_, 1);
lean_inc_ref(v_keys_4721_);
lean_dec_ref(v_toSimprocOLeanEntry_4717_);
v___x_4722_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_4715_, v_keys_4721_, v_declName_4719_, v_post_4720_, v_proc_4718_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2(lean_object* v_e_4723_){
_start:
{
lean_object* v_toSimprocOLeanEntry_4724_; 
v_toSimprocOLeanEntry_4724_ = lean_ctor_get(v_e_4723_, 0);
lean_inc_ref(v_toSimprocOLeanEntry_4724_);
return v_toSimprocOLeanEntry_4724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed(lean_object* v_e_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_Lean_Meta_Simp_mkSimprocExt___lam__2(v_e_4725_);
lean_dec_ref(v_e_4725_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3(lean_object* v_x_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___x_4731_; 
v___x_4731_ = l_Lean_Meta_Simp_toSimprocEntry(v___y_4728_, v___y_4729_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed(lean_object* v_x_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Meta_Simp_mkSimprocExt___lam__3(v_x_4732_, v___y_4733_, v___y_4734_);
lean_dec_ref(v___y_4734_);
lean_dec_ref(v_x_4732_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4(lean_object* v_ref_x3f_4737_){
_start:
{
if (lean_obj_tag(v_ref_x3f_4737_) == 1)
{
lean_object* v_val_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4747_; 
v_val_4739_ = lean_ctor_get(v_ref_x3f_4737_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v_ref_x3f_4737_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4741_ = v_ref_x3f_4737_;
v_isShared_4742_ = v_isSharedCheck_4747_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_val_4739_);
lean_dec(v_ref_x3f_4737_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4747_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4743_ = lean_st_ref_get(v_val_4739_);
lean_dec(v_val_4739_);
if (v_isShared_4742_ == 0)
{
lean_ctor_set_tag(v___x_4741_, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4743_);
v___x_4745_ = v___x_4741_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
else
{
lean_object* v___x_4748_; lean_object* v___x_4749_; 
lean_dec(v_ref_x3f_4737_);
v___x_4748_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4748_);
return v___x_4749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed(lean_object* v_ref_x3f_4750_, lean_object* v___y_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Lean_Meta_Simp_mkSimprocExt___lam__4(v_ref_x3f_4750_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__5(lean_object* v___y_4753_){
_start:
{
lean_inc_ref(v___y_4753_);
return v___y_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__5___boxed(lean_object* v___y_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_Meta_Simp_mkSimprocExt___lam__5(v___y_4754_);
lean_dec_ref(v___y_4754_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object* v_name_4761_, lean_object* v_ref_x3f_4762_){
_start:
{
lean_object* v___f_4764_; lean_object* v___f_4765_; lean_object* v___f_4766_; lean_object* v___f_4767_; lean_object* v___y_4768_; lean_object* v___f_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___f_4764_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__0));
v___f_4765_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__1));
v___f_4766_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__2));
v___f_4767_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__3));
v___y_4768_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed), 2, 1);
lean_closure_set(v___y_4768_, 0, v_ref_x3f_4762_);
v___f_4769_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__4));
v___x_4770_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4770_, 0, v_name_4761_);
lean_ctor_set(v___x_4770_, 1, v___y_4768_);
lean_ctor_set(v___x_4770_, 2, v___f_4767_);
lean_ctor_set(v___x_4770_, 3, v___f_4766_);
lean_ctor_set(v___x_4770_, 4, v___f_4765_);
lean_ctor_set(v___x_4770_, 5, v___f_4769_);
lean_ctor_set(v___x_4770_, 6, v___f_4764_);
v___x_4771_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_4770_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___boxed(lean_object* v_name_4772_, lean_object* v_ref_x3f_4773_, lean_object* v_a_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Meta_Simp_mkSimprocExt(v_name_4772_, v_ref_x3f_4773_);
return v_res_4775_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1);
v___x_4777_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
lean_ctor_set(v___x_4777_, 2, v___x_4776_);
lean_ctor_set(v___x_4777_, 3, v___x_4776_);
lean_ctor_set(v___x_4777_, 4, v___x_4776_);
lean_ctor_set(v___x_4777_, 5, v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__1(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4778_ = lean_unsigned_to_nat(32u);
v___x_4779_ = lean_mk_empty_array_with_capacity(v___x_4778_);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__2(void){
_start:
{
size_t v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4781_ = ((size_t)5ULL);
v___x_4782_ = lean_unsigned_to_nat(0u);
v___x_4783_ = lean_unsigned_to_nat(32u);
v___x_4784_ = lean_mk_empty_array_with_capacity(v___x_4783_);
v___x_4785_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__1, &l_Lean_Meta_Simp_addSimprocAttr___closed__1_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__1);
v___x_4786_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
lean_ctor_set(v___x_4786_, 1, v___x_4784_);
lean_ctor_set(v___x_4786_, 2, v___x_4782_);
lean_ctor_set(v___x_4786_, 3, v___x_4782_);
lean_ctor_set_usize(v___x_4786_, 4, v___x_4781_);
return v___x_4786_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1);
v___x_4788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4787_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
lean_ctor_set(v___x_4788_, 2, v___x_4787_);
lean_ctor_set(v___x_4788_, 3, v___x_4787_);
lean_ctor_set(v___x_4788_, 4, v___x_4787_);
return v___x_4788_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__4(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4789_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__3, &l_Lean_Meta_Simp_addSimprocAttr___closed__3_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__3);
v___x_4790_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__2, &l_Lean_Meta_Simp_addSimprocAttr___closed__2_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__2);
v___x_4791_ = lean_box(1);
v___x_4792_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__0, &l_Lean_Meta_Simp_addSimprocAttr___closed__0_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__0);
v___x_4793_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2);
v___x_4794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
lean_ctor_set(v___x_4794_, 1, v___x_4792_);
lean_ctor_set(v___x_4794_, 2, v___x_4791_);
lean_ctor_set(v___x_4794_, 3, v___x_4790_);
lean_ctor_set(v___x_4794_, 4, v___x_4789_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object* v_attrName_4801_, lean_object* v_ext_4802_, lean_object* v_declName_4803_, lean_object* v_stx_4804_, uint8_t v_attrKind_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v___x_4809_; 
lean_inc(v_declName_4803_);
v___x_4809_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_4801_, v_declName_4803_, v_attrKind_4805_, v_a_4806_, v_a_4807_);
if (lean_obj_tag(v___x_4809_) == 0)
{
uint8_t v___y_4811_; lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; 
lean_dec_ref(v___x_4809_);
v___x_4825_ = lean_unsigned_to_nat(1u);
v___x_4826_ = l_Lean_Syntax_getArg(v_stx_4804_, v___x_4825_);
v___x_4827_ = l_Lean_Syntax_isNone(v___x_4826_);
if (v___x_4827_ == 0)
{
lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; uint8_t v___x_4832_; 
v___x_4828_ = lean_unsigned_to_nat(0u);
v___x_4829_ = l_Lean_Syntax_getArg(v___x_4826_, v___x_4828_);
lean_dec(v___x_4826_);
v___x_4830_ = l_Lean_Syntax_getKind(v___x_4829_);
v___x_4831_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocAttr___closed__6));
v___x_4832_ = lean_name_eq(v___x_4830_, v___x_4831_);
lean_dec(v___x_4830_);
v___y_4811_ = v___x_4832_;
goto v___jp_4810_;
}
else
{
lean_dec(v___x_4826_);
v___y_4811_ = v___x_4827_;
goto v___jp_4810_;
}
v___jp_4810_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v___x_4812_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__4, &l_Lean_Meta_Simp_addSimprocAttr___closed__4_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__4);
v___x_4813_ = lean_st_mk_ref(v___x_4812_);
v___x_4814_ = l_Lean_Meta_Simp_addSimprocAttrCore(v_ext_4802_, v_declName_4803_, v_attrKind_4805_, v___y_4811_, v_a_4806_, v_a_4807_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4823_; 
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4814_);
if (v_isSharedCheck_4823_ == 0)
{
lean_object* v_unused_4824_; 
v_unused_4824_ = lean_ctor_get(v___x_4814_, 0);
lean_dec(v_unused_4824_);
v___x_4816_ = v___x_4814_;
v_isShared_4817_ = v_isSharedCheck_4823_;
goto v_resetjp_4815_;
}
else
{
lean_dec(v___x_4814_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4823_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
v___x_4818_ = lean_st_ref_get(v___x_4813_);
lean_dec(v___x_4813_);
lean_dec(v___x_4818_);
v___x_4819_ = lean_box(0);
if (v_isShared_4817_ == 0)
{
lean_ctor_set(v___x_4816_, 0, v___x_4819_);
v___x_4821_ = v___x_4816_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
else
{
lean_dec(v___x_4813_);
return v___x_4814_;
}
}
}
else
{
lean_dec(v_declName_4803_);
lean_dec_ref(v_ext_4802_);
return v___x_4809_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object* v_attrName_4833_, lean_object* v_ext_4834_, lean_object* v_declName_4835_, lean_object* v_stx_4836_, lean_object* v_attrKind_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_){
_start:
{
uint8_t v_attrKind_boxed_4841_; lean_object* v_res_4842_; 
v_attrKind_boxed_4841_ = lean_unbox(v_attrKind_4837_);
v_res_4842_ = l_Lean_Meta_Simp_addSimprocAttr(v_attrName_4833_, v_ext_4834_, v_declName_4835_, v_stx_4836_, v_attrKind_boxed_4841_, v_a_4838_, v_a_4839_);
lean_dec(v_a_4839_);
lean_dec_ref(v_a_4838_);
lean_dec(v_stx_4836_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object* v_attrName_4843_, lean_object* v_attrDescr_4844_, lean_object* v_ext_4845_, lean_object* v_name_4846_){
_start:
{
uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; 
v___x_4848_ = 1;
lean_inc(v_attrName_4843_);
v___x_4849_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4849_, 0, v_name_4846_);
lean_ctor_set(v___x_4849_, 1, v_attrName_4843_);
lean_ctor_set(v___x_4849_, 2, v_attrDescr_4844_);
lean_ctor_set_uint8(v___x_4849_, sizeof(void*)*3, v___x_4848_);
lean_inc_ref(v_ext_4845_);
v___x_4850_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_addSimprocAttr___boxed), 8, 2);
lean_closure_set(v___x_4850_, 0, v_attrName_4843_);
lean_closure_set(v___x_4850_, 1, v_ext_4845_);
v___x_4851_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___boxed), 5, 1);
lean_closure_set(v___x_4851_, 0, v_ext_4845_);
v___x_4852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4849_);
lean_ctor_set(v___x_4852_, 1, v___x_4850_);
lean_ctor_set(v___x_4852_, 2, v___x_4851_);
v___x_4853_ = l_Lean_registerBuiltinAttribute(v___x_4852_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr___boxed(lean_object* v_attrName_4854_, lean_object* v_attrDescr_4855_, lean_object* v_ext_4856_, lean_object* v_name_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_Meta_Simp_mkSimprocAttr(v_attrName_4854_, v_attrDescr_4855_, v_ext_4856_, v_name_4857_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4861_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1);
v___x_4862_ = lean_st_mk_ref(v___x_4861_);
v___x_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4863_, 0, v___x_4862_);
return v___x_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2____boxed(lean_object* v_a_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2_();
return v_res_4865_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimprocAttr___auto__1(void){
_start:
{
lean_object* v___x_4866_; 
v___x_4866_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26);
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object* v_attrName_4867_, lean_object* v_attrDescr_4868_, lean_object* v_ref_x3f_4869_, lean_object* v_name_4870_){
_start:
{
lean_object* v___x_4872_; 
lean_inc(v_name_4870_);
v___x_4872_ = l_Lean_Meta_Simp_mkSimprocExt(v_name_4870_, v_ref_x3f_4869_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref(v___x_4872_);
lean_inc(v_a_4873_);
lean_inc(v_attrName_4867_);
v___x_4874_ = l_Lean_Meta_Simp_mkSimprocAttr(v_attrName_4867_, v_attrDescr_4868_, v_a_4873_, v_name_4870_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4885_; 
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4885_ == 0)
{
lean_object* v_unused_4886_; 
v_unused_4886_ = lean_ctor_get(v___x_4874_, 0);
lean_dec(v_unused_4886_);
v___x_4876_ = v___x_4874_;
v_isShared_4877_ = v_isSharedCheck_4885_;
goto v_resetjp_4875_;
}
else
{
lean_dec(v___x_4874_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4885_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4878_ = l_Lean_Meta_Simp_simprocExtensionMapRef;
v___x_4879_ = lean_st_ref_take(v___x_4878_);
lean_inc(v_a_4873_);
v___x_4880_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(v___x_4879_, v_attrName_4867_, v_a_4873_);
v___x_4881_ = lean_st_ref_set(v___x_4878_, v___x_4880_);
if (v_isShared_4877_ == 0)
{
lean_ctor_set(v___x_4876_, 0, v_a_4873_);
v___x_4883_ = v___x_4876_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4873_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v_a_4873_);
lean_dec(v_attrName_4867_);
v_a_4887_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4874_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4874_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
else
{
lean_dec(v_name_4870_);
lean_dec_ref(v_attrDescr_4868_);
lean_dec(v_attrName_4867_);
return v___x_4872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr___boxed(lean_object* v_attrName_4895_, lean_object* v_attrDescr_4896_, lean_object* v_ref_x3f_4897_, lean_object* v_name_4898_, lean_object* v_a_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l_Lean_Meta_Simp_registerSimprocAttr(v_attrName_4895_, v_attrDescr_4896_, v_ref_x3f_4897_, v_name_4898_);
return v_res_4900_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = l_Lean_Meta_Simp_builtinSimprocsRef;
v___x_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4905_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4914_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
v___x_4915_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
v___x_4916_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_);
v___x_4917_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
v___x_4918_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_4914_, v___x_4915_, v___x_4916_, v___x_4917_);
return v___x_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2____boxed(lean_object* v_a_4919_){
_start:
{
lean_object* v_res_4920_; 
v_res_4920_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_();
return v_res_4920_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4925_ = l_Lean_Meta_Simp_builtinSEvalprocsRef;
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
return v___x_4926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4934_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
v___x_4935_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
v___x_4936_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_);
v___x_4937_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
v___x_4938_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_4934_, v___x_4935_, v___x_4936_, v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2____boxed(lean_object* v_a_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_();
return v_res_4940_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v___x_4949_ = lean_box(0);
v___x_4950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4));
v___x_4951_ = l_Lean_mkConst(v___x_4950_, v___x_4949_);
return v___x_4951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; 
v___x_4956_ = lean_box(0);
v___x_4957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7));
v___x_4958_ = l_Lean_mkConst(v___x_4957_, v___x_4956_);
return v___x_4958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(lean_object* v_addDeclName_4959_, lean_object* v_declName_4960_, uint8_t v___y_4961_, lean_object* v_procExpr_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___y_4972_; 
v___x_4968_ = lean_box(0);
v___x_4969_ = l_Lean_mkConst(v_addDeclName_4959_, v___x_4968_);
lean_inc(v_declName_4960_);
v___x_4970_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_4960_);
if (v___y_4961_ == 0)
{
lean_object* v___x_4992_; 
v___x_4992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5);
v___y_4972_ = v___x_4992_;
goto v___jp_4971_;
}
else
{
lean_object* v___x_4993_; 
v___x_4993_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8);
v___y_4972_ = v___x_4993_;
goto v___jp_4971_;
}
v___jp_4971_:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v___x_4973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__1));
v___x_4974_ = l_Lean_Name_append(v_declName_4960_, v___x_4973_);
v___x_4975_ = l_Lean_Core_mkFreshUserName(v___x_4974_, v___y_4965_, v___y_4966_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref(v___x_4975_);
v___x_4977_ = lean_unsigned_to_nat(3u);
v___x_4978_ = lean_mk_empty_array_with_capacity(v___x_4977_);
v___x_4979_ = lean_array_push(v___x_4978_, v___x_4970_);
v___x_4980_ = lean_array_push(v___x_4979_, v___y_4972_);
v___x_4981_ = lean_array_push(v___x_4980_, v_procExpr_4962_);
v___x_4982_ = l_Lean_mkAppN(v___x_4969_, v___x_4981_);
lean_dec_ref(v___x_4981_);
v___x_4983_ = l_Lean_declareBuiltin(v_a_4976_, v___x_4982_, v___y_4965_, v___y_4966_);
return v___x_4983_;
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
lean_dec_ref(v___y_4972_);
lean_dec_ref(v___x_4970_);
lean_dec_ref(v___x_4969_);
lean_dec_ref(v_procExpr_4962_);
v_a_4984_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4975_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4975_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed(lean_object* v_addDeclName_4994_, lean_object* v_declName_4995_, lean_object* v___y_4996_, lean_object* v_procExpr_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
uint8_t v___y_4474__boxed_5003_; lean_object* v_res_5004_; 
v___y_4474__boxed_5003_ = lean_unbox(v___y_4996_);
v_res_5004_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(v_addDeclName_4994_, v_declName_4995_, v___y_4474__boxed_5003_, v_procExpr_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(lean_object* v_msg_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_ref_5011_; lean_object* v___x_5012_; lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5021_; 
v_ref_5011_ = lean_ctor_get(v___y_5008_, 5);
v___x_5012_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1(v_msg_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5021_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5021_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
lean_inc(v_ref_5011_);
v___x_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5017_, 0, v_ref_5011_);
lean_ctor_set(v___x_5017_, 1, v_a_5013_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set_tag(v___x_5015_, 1);
lean_ctor_set(v___x_5015_, 0, v___x_5017_);
v___x_5019_ = v___x_5015_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg___boxed(lean_object* v_msg_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v_msg_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
return v_res_5028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5030_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__0));
v___x_5031_ = l_Lean_stringToMessageData(v___x_5030_);
return v___x_5031_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3(void){
_start:
{
uint8_t v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5037_ = 0;
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2));
v___x_5039_ = l_Lean_MessageData_ofConstName(v___x_5038_, v___x_5037_);
return v___x_5039_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3);
v___x_5041_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1);
v___x_5042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5041_);
lean_ctor_set(v___x_5042_, 1, v___x_5040_);
return v___x_5042_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__5));
v___x_5045_ = l_Lean_stringToMessageData(v___x_5044_);
return v___x_5045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7(void){
_start:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5046_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6);
v___x_5047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4);
v___x_5048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5048_, 0, v___x_5047_);
lean_ctor_set(v___x_5048_, 1, v___x_5046_);
return v___x_5048_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9(void){
_start:
{
uint8_t v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; 
v___x_5054_ = 0;
v___x_5055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8));
v___x_5056_ = l_Lean_MessageData_ofConstName(v___x_5055_, v___x_5054_);
return v___x_5056_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10(void){
_start:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9);
v___x_5058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7);
v___x_5059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5058_);
lean_ctor_set(v___x_5059_, 1, v___x_5057_);
return v___x_5059_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__11));
v___x_5062_ = l_Lean_stringToMessageData(v___x_5061_);
return v___x_5062_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13(void){
_start:
{
lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12);
v___x_5064_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10);
v___x_5065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5064_);
lean_ctor_set(v___x_5065_, 1, v___x_5063_);
return v___x_5065_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__14));
v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(lean_object* v_declName_5069_, lean_object* v___f_5070_, lean_object* v_tp_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
uint8_t v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
v___x_5077_ = 0;
v___x_5078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13);
v___x_5079_ = l_Lean_MessageData_ofConstName(v_declName_5069_, v___x_5077_);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5078_);
lean_ctor_set(v___x_5080_, 1, v___x_5079_);
v___x_5081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15);
v___x_5082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5082_, 0, v___x_5080_);
lean_ctor_set(v___x_5082_, 1, v___x_5081_);
v___x_5083_ = l_Lean_indentExpr(v_tp_5071_);
v___x_5084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5084_, 0, v___x_5082_);
lean_ctor_set(v___x_5084_, 1, v___x_5083_);
v___x_5085_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v___x_5084_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5085_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5085_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___boxed(lean_object* v_declName_5094_, lean_object* v___f_5095_, lean_object* v_tp_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5094_, v___f_5095_, v_tp_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec_ref(v___f_5095_);
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_5103_, lean_object* v_msg_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_fileName_5110_; lean_object* v_fileMap_5111_; lean_object* v_options_5112_; lean_object* v_currRecDepth_5113_; lean_object* v_maxRecDepth_5114_; lean_object* v_ref_5115_; lean_object* v_currNamespace_5116_; lean_object* v_openDecls_5117_; lean_object* v_initHeartbeats_5118_; lean_object* v_maxHeartbeats_5119_; lean_object* v_quotContext_5120_; lean_object* v_currMacroScope_5121_; uint8_t v_diag_5122_; lean_object* v_cancelTk_x3f_5123_; uint8_t v_suppressElabErrors_5124_; lean_object* v_inheritedTraceOptions_5125_; lean_object* v_ref_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; 
v_fileName_5110_ = lean_ctor_get(v___y_5107_, 0);
v_fileMap_5111_ = lean_ctor_get(v___y_5107_, 1);
v_options_5112_ = lean_ctor_get(v___y_5107_, 2);
v_currRecDepth_5113_ = lean_ctor_get(v___y_5107_, 3);
v_maxRecDepth_5114_ = lean_ctor_get(v___y_5107_, 4);
v_ref_5115_ = lean_ctor_get(v___y_5107_, 5);
v_currNamespace_5116_ = lean_ctor_get(v___y_5107_, 6);
v_openDecls_5117_ = lean_ctor_get(v___y_5107_, 7);
v_initHeartbeats_5118_ = lean_ctor_get(v___y_5107_, 8);
v_maxHeartbeats_5119_ = lean_ctor_get(v___y_5107_, 9);
v_quotContext_5120_ = lean_ctor_get(v___y_5107_, 10);
v_currMacroScope_5121_ = lean_ctor_get(v___y_5107_, 11);
v_diag_5122_ = lean_ctor_get_uint8(v___y_5107_, sizeof(void*)*14);
v_cancelTk_x3f_5123_ = lean_ctor_get(v___y_5107_, 12);
v_suppressElabErrors_5124_ = lean_ctor_get_uint8(v___y_5107_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5125_ = lean_ctor_get(v___y_5107_, 13);
v_ref_5126_ = l_Lean_replaceRef(v_ref_5103_, v_ref_5115_);
lean_inc_ref(v_inheritedTraceOptions_5125_);
lean_inc(v_cancelTk_x3f_5123_);
lean_inc(v_currMacroScope_5121_);
lean_inc(v_quotContext_5120_);
lean_inc(v_maxHeartbeats_5119_);
lean_inc(v_initHeartbeats_5118_);
lean_inc(v_openDecls_5117_);
lean_inc(v_currNamespace_5116_);
lean_inc(v_maxRecDepth_5114_);
lean_inc(v_currRecDepth_5113_);
lean_inc_ref(v_options_5112_);
lean_inc_ref(v_fileMap_5111_);
lean_inc_ref(v_fileName_5110_);
v___x_5127_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5127_, 0, v_fileName_5110_);
lean_ctor_set(v___x_5127_, 1, v_fileMap_5111_);
lean_ctor_set(v___x_5127_, 2, v_options_5112_);
lean_ctor_set(v___x_5127_, 3, v_currRecDepth_5113_);
lean_ctor_set(v___x_5127_, 4, v_maxRecDepth_5114_);
lean_ctor_set(v___x_5127_, 5, v_ref_5126_);
lean_ctor_set(v___x_5127_, 6, v_currNamespace_5116_);
lean_ctor_set(v___x_5127_, 7, v_openDecls_5117_);
lean_ctor_set(v___x_5127_, 8, v_initHeartbeats_5118_);
lean_ctor_set(v___x_5127_, 9, v_maxHeartbeats_5119_);
lean_ctor_set(v___x_5127_, 10, v_quotContext_5120_);
lean_ctor_set(v___x_5127_, 11, v_currMacroScope_5121_);
lean_ctor_set(v___x_5127_, 12, v_cancelTk_x3f_5123_);
lean_ctor_set(v___x_5127_, 13, v_inheritedTraceOptions_5125_);
lean_ctor_set_uint8(v___x_5127_, sizeof(void*)*14, v_diag_5122_);
lean_ctor_set_uint8(v___x_5127_, sizeof(void*)*14 + 1, v_suppressElabErrors_5124_);
v___x_5128_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v_msg_5104_, v___y_5105_, v___y_5106_, v___x_5127_, v___y_5108_);
lean_dec_ref(v___x_5127_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_5129_, lean_object* v_msg_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_){
_start:
{
lean_object* v_res_5136_; 
v_res_5136_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5129_, v_msg_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
lean_dec(v___y_5134_);
lean_dec_ref(v___y_5133_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
lean_dec(v_ref_5129_);
return v_res_5136_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; 
v___x_5138_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_5139_ = l_Lean_stringToMessageData(v___x_5138_);
return v___x_5139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; 
v___x_5141_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_5142_ = l_Lean_stringToMessageData(v___x_5141_);
return v___x_5142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_5145_ = l_Lean_stringToMessageData(v___x_5144_);
return v___x_5145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5147_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_5148_ = l_Lean_stringToMessageData(v___x_5147_);
return v___x_5148_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5150_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_5151_ = l_Lean_stringToMessageData(v___x_5150_);
return v___x_5151_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5153_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_5154_ = l_Lean_stringToMessageData(v___x_5153_);
return v___x_5154_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5156_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_5157_ = l_Lean_stringToMessageData(v___x_5156_);
return v___x_5157_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_5158_, lean_object* v_declHint_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v___x_5162_; lean_object* v_env_5163_; uint8_t v___x_5164_; 
v___x_5162_ = lean_st_ref_get(v___y_5160_);
v_env_5163_ = lean_ctor_get(v___x_5162_, 0);
lean_inc_ref(v_env_5163_);
lean_dec(v___x_5162_);
v___x_5164_ = l_Lean_Name_isAnonymous(v_declHint_5159_);
if (v___x_5164_ == 0)
{
uint8_t v_isExporting_5165_; 
v_isExporting_5165_ = lean_ctor_get_uint8(v_env_5163_, sizeof(void*)*8);
if (v_isExporting_5165_ == 0)
{
lean_object* v___x_5166_; 
lean_dec_ref(v_env_5163_);
lean_dec(v_declHint_5159_);
v___x_5166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5166_, 0, v_msg_5158_);
return v___x_5166_;
}
else
{
lean_object* v___x_5167_; uint8_t v___x_5168_; 
lean_inc_ref(v_env_5163_);
v___x_5167_ = l_Lean_Environment_setExporting(v_env_5163_, v___x_5164_);
lean_inc(v_declHint_5159_);
lean_inc_ref(v___x_5167_);
v___x_5168_ = l_Lean_Environment_contains(v___x_5167_, v_declHint_5159_, v_isExporting_5165_);
if (v___x_5168_ == 0)
{
lean_object* v___x_5169_; 
lean_dec_ref(v___x_5167_);
lean_dec_ref(v_env_5163_);
lean_dec(v_declHint_5159_);
v___x_5169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5169_, 0, v_msg_5158_);
return v___x_5169_;
}
else
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v_c_5175_; lean_object* v___x_5176_; 
v___x_5170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2);
v___x_5171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5);
v___x_5172_ = l_Lean_Options_empty;
v___x_5173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5173_, 0, v___x_5167_);
lean_ctor_set(v___x_5173_, 1, v___x_5170_);
lean_ctor_set(v___x_5173_, 2, v___x_5171_);
lean_ctor_set(v___x_5173_, 3, v___x_5172_);
lean_inc(v_declHint_5159_);
v___x_5174_ = l_Lean_MessageData_ofConstName(v_declHint_5159_, v___x_5164_);
v_c_5175_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_5175_, 0, v___x_5173_);
lean_ctor_set(v_c_5175_, 1, v___x_5174_);
v___x_5176_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5163_, v_declHint_5159_);
if (lean_obj_tag(v___x_5176_) == 0)
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_dec_ref(v_env_5163_);
lean_dec(v_declHint_5159_);
v___x_5177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_5178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5178_, 0, v___x_5177_);
lean_ctor_set(v___x_5178_, 1, v_c_5175_);
v___x_5179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_5180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5180_, 0, v___x_5178_);
lean_ctor_set(v___x_5180_, 1, v___x_5179_);
v___x_5181_ = l_Lean_MessageData_note(v___x_5180_);
v___x_5182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5182_, 0, v_msg_5158_);
lean_ctor_set(v___x_5182_, 1, v___x_5181_);
v___x_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
return v___x_5183_;
}
else
{
lean_object* v_val_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5219_; 
v_val_5184_ = lean_ctor_get(v___x_5176_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5176_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5186_ = v___x_5176_;
v_isShared_5187_ = v_isSharedCheck_5219_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_val_5184_);
lean_dec(v___x_5176_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5219_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v_mod_5191_; uint8_t v___x_5192_; 
v___x_5188_ = lean_box(0);
v___x_5189_ = l_Lean_Environment_header(v_env_5163_);
lean_dec_ref(v_env_5163_);
v___x_5190_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5189_);
v_mod_5191_ = lean_array_get(v___x_5188_, v___x_5190_, v_val_5184_);
lean_dec(v_val_5184_);
lean_dec_ref(v___x_5190_);
v___x_5192_ = l_Lean_isPrivateName(v_declHint_5159_);
lean_dec(v_declHint_5159_);
if (v___x_5192_ == 0)
{
lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5204_; 
v___x_5193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_5194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5193_);
lean_ctor_set(v___x_5194_, 1, v_c_5175_);
v___x_5195_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_5196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5194_);
lean_ctor_set(v___x_5196_, 1, v___x_5195_);
v___x_5197_ = l_Lean_MessageData_ofName(v_mod_5191_);
v___x_5198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5198_, 0, v___x_5196_);
lean_ctor_set(v___x_5198_, 1, v___x_5197_);
v___x_5199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_5200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5198_);
lean_ctor_set(v___x_5200_, 1, v___x_5199_);
v___x_5201_ = l_Lean_MessageData_note(v___x_5200_);
v___x_5202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5202_, 0, v_msg_5158_);
lean_ctor_set(v___x_5202_, 1, v___x_5201_);
if (v_isShared_5187_ == 0)
{
lean_ctor_set_tag(v___x_5186_, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5202_);
v___x_5204_ = v___x_5186_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v___x_5202_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5217_; 
v___x_5206_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_5207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5206_);
lean_ctor_set(v___x_5207_, 1, v_c_5175_);
v___x_5208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_5209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5209_, 0, v___x_5207_);
lean_ctor_set(v___x_5209_, 1, v___x_5208_);
v___x_5210_ = l_Lean_MessageData_ofName(v_mod_5191_);
v___x_5211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5211_, 0, v___x_5209_);
lean_ctor_set(v___x_5211_, 1, v___x_5210_);
v___x_5212_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_5213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5213_, 0, v___x_5211_);
lean_ctor_set(v___x_5213_, 1, v___x_5212_);
v___x_5214_ = l_Lean_MessageData_note(v___x_5213_);
v___x_5215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5215_, 0, v_msg_5158_);
lean_ctor_set(v___x_5215_, 1, v___x_5214_);
if (v_isShared_5187_ == 0)
{
lean_ctor_set_tag(v___x_5186_, 0);
lean_ctor_set(v___x_5186_, 0, v___x_5215_);
v___x_5217_ = v___x_5186_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5215_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5220_; 
lean_dec_ref(v_env_5163_);
lean_dec(v_declHint_5159_);
v___x_5220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5220_, 0, v_msg_5158_);
return v___x_5220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_5221_, lean_object* v_declHint_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_){
_start:
{
lean_object* v_res_5225_; 
v_res_5225_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5221_, v_declHint_5222_, v___y_5223_);
lean_dec(v___y_5223_);
return v_res_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_5226_, lean_object* v_declHint_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_){
_start:
{
lean_object* v___x_5233_; lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5243_; 
v___x_5233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5226_, v_declHint_5227_, v___y_5231_);
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5243_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5243_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5241_; 
v___x_5238_ = l_Lean_unknownIdentifierMessageTag;
v___x_5239_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5238_);
lean_ctor_set(v___x_5239_, 1, v_a_5234_);
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 0, v___x_5239_);
v___x_5241_ = v___x_5236_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_5244_, lean_object* v_declHint_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(v_msg_5244_, v_declHint_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_5252_, lean_object* v_msg_5253_, lean_object* v_declHint_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v___x_5260_; lean_object* v_a_5261_; lean_object* v___x_5262_; 
v___x_5260_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(v_msg_5253_, v_declHint_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc(v_a_5261_);
lean_dec_ref(v___x_5260_);
v___x_5262_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5252_, v_a_5261_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_5263_, lean_object* v_msg_5264_, lean_object* v_declHint_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_5263_, v_msg_5264_, v_declHint_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
lean_dec(v___y_5269_);
lean_dec_ref(v___y_5268_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v_ref_5263_);
return v_res_5271_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5272_; lean_object* v___x_5273_; 
v___x_5272_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__0));
v___x_5273_ = l_Lean_stringToMessageData(v___x_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_5274_, lean_object* v_constName_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; uint8_t v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; 
v___x_5281_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_5282_ = 0;
lean_inc(v_constName_5275_);
v___x_5283_ = l_Lean_MessageData_ofConstName(v_constName_5275_, v___x_5282_);
v___x_5284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5284_, 0, v___x_5281_);
lean_ctor_set(v___x_5284_, 1, v___x_5283_);
v___x_5285_ = lean_obj_once(&l_Lean_Meta_Simp_eraseSimprocAttr___closed__0, &l_Lean_Meta_Simp_eraseSimprocAttr___closed__0_once, _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__0);
v___x_5286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5286_, 0, v___x_5284_);
lean_ctor_set(v___x_5286_, 1, v___x_5285_);
v___x_5287_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_5274_, v___x_5286_, v_constName_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_5288_, lean_object* v_constName_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(v_ref_5288_, v_constName_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec(v_ref_5288_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(lean_object* v_constName_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v_ref_5302_; lean_object* v___x_5303_; 
v_ref_5302_ = lean_ctor_get(v___y_5299_, 5);
v___x_5303_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(v_ref_5302_, v_constName_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
return v___x_5303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg___boxed(lean_object* v_constName_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(v_constName_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(lean_object* v_constName_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v___x_5317_; lean_object* v_env_5318_; uint8_t v___x_5319_; lean_object* v___x_5320_; 
v___x_5317_ = lean_st_ref_get(v___y_5315_);
v_env_5318_ = lean_ctor_get(v___x_5317_, 0);
lean_inc_ref(v_env_5318_);
lean_dec(v___x_5317_);
v___x_5319_ = 0;
lean_inc(v_constName_5311_);
v___x_5320_ = l_Lean_Environment_find_x3f(v_env_5318_, v_constName_5311_, v___x_5319_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v___x_5321_; 
v___x_5321_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(v_constName_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_);
return v___x_5321_;
}
else
{
lean_object* v_val_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
lean_dec(v_constName_5311_);
v_val_5322_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5320_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_val_5322_);
lean_dec(v___x_5320_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
lean_ctor_set_tag(v___x_5324_, 0);
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_val_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1___boxed(lean_object* v_constName_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(v_constName_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
return v_res_5336_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1(void){
_start:
{
lean_object* v___x_5343_; uint64_t v___x_5344_; 
v___x_5343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0));
v___x_5344_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5343_);
return v___x_5344_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2(void){
_start:
{
uint64_t v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5345_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1);
v___x_5346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0));
v___x_5347_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5347_, 0, v___x_5346_);
lean_ctor_set_uint64(v___x_5347_, sizeof(void*)*1, v___x_5345_);
return v___x_5347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3(void){
_start:
{
lean_object* v___x_5348_; 
v___x_5348_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5348_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4(void){
_start:
{
lean_object* v___x_5349_; lean_object* v___x_5350_; 
v___x_5349_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3);
v___x_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5350_, 0, v___x_5349_);
return v___x_5350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; 
v___x_5351_ = lean_box(1);
v___x_5352_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4);
v___x_5353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4);
v___x_5354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5354_, 0, v___x_5353_);
lean_ctor_set(v___x_5354_, 1, v___x_5352_);
lean_ctor_set(v___x_5354_, 2, v___x_5351_);
return v___x_5354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7(void){
_start:
{
uint8_t v___x_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; uint8_t v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
v___x_5357_ = 1;
v___x_5358_ = lean_unsigned_to_nat(0u);
v___x_5359_ = lean_box(0);
v___x_5360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6));
v___x_5361_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5);
v___x_5362_ = lean_box(1);
v___x_5363_ = 0;
v___x_5364_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2);
v___x_5365_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5365_, 0, v___x_5364_);
lean_ctor_set(v___x_5365_, 1, v___x_5362_);
lean_ctor_set(v___x_5365_, 2, v___x_5361_);
lean_ctor_set(v___x_5365_, 3, v___x_5360_);
lean_ctor_set(v___x_5365_, 4, v___x_5359_);
lean_ctor_set(v___x_5365_, 5, v___x_5358_);
lean_ctor_set(v___x_5365_, 6, v___x_5359_);
lean_ctor_set_uint8(v___x_5365_, sizeof(void*)*7, v___x_5363_);
lean_ctor_set_uint8(v___x_5365_, sizeof(void*)*7 + 1, v___x_5363_);
lean_ctor_set_uint8(v___x_5365_, sizeof(void*)*7 + 2, v___x_5363_);
lean_ctor_set_uint8(v___x_5365_, sizeof(void*)*7 + 3, v___x_5357_);
return v___x_5365_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8(void){
_start:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; 
v___x_5366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4);
v___x_5367_ = lean_unsigned_to_nat(0u);
v___x_5368_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5367_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
lean_ctor_set(v___x_5368_, 2, v___x_5367_);
lean_ctor_set(v___x_5368_, 3, v___x_5366_);
lean_ctor_set(v___x_5368_, 4, v___x_5366_);
lean_ctor_set(v___x_5368_, 5, v___x_5366_);
lean_ctor_set(v___x_5368_, 6, v___x_5366_);
lean_ctor_set(v___x_5368_, 7, v___x_5366_);
lean_ctor_set(v___x_5368_, 8, v___x_5366_);
return v___x_5368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9(void){
_start:
{
lean_object* v___x_5369_; lean_object* v___x_5370_; 
v___x_5369_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4);
v___x_5370_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5370_, 0, v___x_5369_);
lean_ctor_set(v___x_5370_, 1, v___x_5369_);
lean_ctor_set(v___x_5370_, 2, v___x_5369_);
lean_ctor_set(v___x_5370_, 3, v___x_5369_);
lean_ctor_set(v___x_5370_, 4, v___x_5369_);
lean_ctor_set(v___x_5370_, 5, v___x_5369_);
return v___x_5370_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10(void){
_start:
{
lean_object* v___x_5371_; lean_object* v___x_5372_; 
v___x_5371_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4);
v___x_5372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5372_, 0, v___x_5371_);
lean_ctor_set(v___x_5372_, 1, v___x_5371_);
lean_ctor_set(v___x_5372_, 2, v___x_5371_);
lean_ctor_set(v___x_5372_, 3, v___x_5371_);
lean_ctor_set(v___x_5372_, 4, v___x_5371_);
return v___x_5372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11(void){
_start:
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5373_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10);
v___x_5374_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4);
v___x_5375_ = lean_box(1);
v___x_5376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9);
v___x_5377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8);
v___x_5378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5378_, 0, v___x_5377_);
lean_ctor_set(v___x_5378_, 1, v___x_5376_);
lean_ctor_set(v___x_5378_, 2, v___x_5375_);
lean_ctor_set(v___x_5378_, 3, v___x_5374_);
lean_ctor_set(v___x_5378_, 4, v___x_5373_);
return v___x_5378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15(void){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; 
v___x_5384_ = lean_unsigned_to_nat(0u);
v___x_5385_ = l_Lean_Level_ofNat(v___x_5384_);
return v___x_5385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16(void){
_start:
{
lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5386_ = lean_box(0);
v___x_5387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15);
v___x_5388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5387_);
lean_ctor_set(v___x_5388_, 1, v___x_5386_);
return v___x_5388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17(void){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16);
v___x_5390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15);
v___x_5391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5390_);
lean_ctor_set(v___x_5391_, 1, v___x_5389_);
return v___x_5391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18(void){
_start:
{
lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; 
v___x_5392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17);
v___x_5393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14));
v___x_5394_ = l_Lean_mkConst(v___x_5393_, v___x_5392_);
return v___x_5394_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19(void){
_start:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; 
v___x_5395_ = lean_box(0);
v___x_5396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2));
v___x_5397_ = l_Lean_mkConst(v___x_5396_, v___x_5395_);
return v___x_5397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20(void){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; 
v___x_5398_ = lean_box(0);
v___x_5399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8));
v___x_5400_ = l_Lean_mkConst(v___x_5399_, v___x_5398_);
return v___x_5400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__23(void){
_start:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17);
v___x_5406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__22));
v___x_5407_ = l_Lean_mkConst(v___x_5406_, v___x_5405_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object* v_declName_5408_, lean_object* v_stx_5409_, lean_object* v_addDeclName_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_){
_start:
{
lean_object* v___y_5415_; lean_object* v___y_5416_; lean_object* v___x_5426_; lean_object* v___x_5427_; uint8_t v___x_5428_; uint8_t v___x_5429_; uint8_t v___y_5431_; 
v___x_5426_ = lean_unsigned_to_nat(1u);
v___x_5427_ = l_Lean_Syntax_getArg(v_stx_5409_, v___x_5426_);
v___x_5428_ = l_Lean_Syntax_isNone(v___x_5427_);
v___x_5429_ = 1;
if (v___x_5428_ == 0)
{
lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; uint8_t v___x_5511_; 
v___x_5507_ = lean_unsigned_to_nat(0u);
v___x_5508_ = l_Lean_Syntax_getArg(v___x_5427_, v___x_5507_);
lean_dec(v___x_5427_);
v___x_5509_ = l_Lean_Syntax_getKind(v___x_5508_);
v___x_5510_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocAttr___closed__6));
v___x_5511_ = lean_name_eq(v___x_5509_, v___x_5510_);
lean_dec(v___x_5509_);
v___y_5431_ = v___x_5511_;
goto v___jp_5430_;
}
else
{
lean_dec(v___x_5427_);
v___y_5431_ = v___x_5429_;
goto v___jp_5430_;
}
v___jp_5414_:
{
if (lean_obj_tag(v___y_5416_) == 0)
{
lean_object* v_a_5417_; lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5425_; 
v_a_5417_ = lean_ctor_get(v___y_5416_, 0);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___y_5416_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5419_ = v___y_5416_;
v_isShared_5420_ = v_isSharedCheck_5425_;
goto v_resetjp_5418_;
}
else
{
lean_inc(v_a_5417_);
lean_dec(v___y_5416_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5425_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v___x_5421_; lean_object* v___x_5423_; 
v___x_5421_ = lean_st_ref_get(v___y_5415_);
lean_dec(v___y_5415_);
lean_dec(v___x_5421_);
if (v_isShared_5420_ == 0)
{
v___x_5423_ = v___x_5419_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_a_5417_);
v___x_5423_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
return v___x_5423_;
}
}
}
else
{
lean_dec(v___y_5415_);
return v___y_5416_;
}
}
v___jp_5430_:
{
lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7);
v___x_5433_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11);
v___x_5434_ = lean_st_mk_ref(v___x_5433_);
lean_inc(v_declName_5408_);
v___x_5435_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(v_declName_5408_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; lean_object* v___f_5438_; lean_object* v___x_5439_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref(v___x_5435_);
v___x_5437_ = lean_box(v___y_5431_);
lean_inc(v_declName_5408_);
lean_inc(v_addDeclName_5410_);
v___f_5438_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed), 9, 3);
lean_closure_set(v___f_5438_, 0, v_addDeclName_5410_);
lean_closure_set(v___f_5438_, 1, v_declName_5408_);
lean_closure_set(v___f_5438_, 2, v___x_5437_);
v___x_5439_ = l_Lean_ConstantInfo_type(v_a_5436_);
lean_dec(v_a_5436_);
if (lean_obj_tag(v___x_5439_) == 4)
{
lean_object* v_declName_5440_; 
v_declName_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_declName_5440_);
if (lean_obj_tag(v_declName_5440_) == 1)
{
lean_object* v_pre_5441_; 
v_pre_5441_ = lean_ctor_get(v_declName_5440_, 0);
lean_inc(v_pre_5441_);
if (lean_obj_tag(v_pre_5441_) == 1)
{
lean_object* v_pre_5442_; 
v_pre_5442_ = lean_ctor_get(v_pre_5441_, 0);
lean_inc(v_pre_5442_);
if (lean_obj_tag(v_pre_5442_) == 1)
{
lean_object* v_pre_5443_; 
v_pre_5443_ = lean_ctor_get(v_pre_5442_, 0);
lean_inc(v_pre_5443_);
if (lean_obj_tag(v_pre_5443_) == 1)
{
lean_object* v_pre_5444_; 
v_pre_5444_ = lean_ctor_get(v_pre_5443_, 0);
lean_inc(v_pre_5444_);
if (lean_obj_tag(v_pre_5444_) == 0)
{
lean_object* v_us_5445_; lean_object* v_str_5446_; lean_object* v_str_5447_; lean_object* v_str_5448_; lean_object* v_str_5449_; lean_object* v___x_5450_; uint8_t v___x_5451_; 
v_us_5445_ = lean_ctor_get(v___x_5439_, 1);
lean_inc(v_us_5445_);
v_str_5446_ = lean_ctor_get(v_declName_5440_, 1);
lean_inc_ref(v_str_5446_);
lean_dec_ref(v_declName_5440_);
v_str_5447_ = lean_ctor_get(v_pre_5441_, 1);
lean_inc_ref(v_str_5447_);
lean_dec_ref(v_pre_5441_);
v_str_5448_ = lean_ctor_get(v_pre_5442_, 1);
lean_inc_ref(v_str_5448_);
lean_dec_ref(v_pre_5442_);
v_str_5449_ = lean_ctor_get(v_pre_5443_, 1);
lean_inc_ref(v_str_5449_);
lean_dec_ref(v_pre_5443_);
v___x_5450_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_5451_ = lean_string_dec_eq(v_str_5449_, v___x_5450_);
lean_dec_ref(v_str_5449_);
if (v___x_5451_ == 0)
{
lean_object* v___x_5452_; 
lean_dec_ref(v_str_5448_);
lean_dec_ref(v_str_5447_);
lean_dec_ref(v_str_5446_);
lean_dec(v_us_5445_);
lean_dec(v_addDeclName_5410_);
v___x_5452_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5452_;
goto v___jp_5414_;
}
else
{
lean_object* v___x_5453_; uint8_t v___x_5454_; 
lean_dec_ref(v___x_5439_);
v___x_5453_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_5454_ = lean_string_dec_eq(v_str_5448_, v___x_5453_);
if (v___x_5454_ == 0)
{
lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; 
lean_dec(v_addDeclName_5410_);
v___x_5455_ = l_Lean_Name_str___override(v_pre_5444_, v___x_5450_);
v___x_5456_ = l_Lean_Name_str___override(v___x_5455_, v_str_5448_);
v___x_5457_ = l_Lean_Name_str___override(v___x_5456_, v_str_5447_);
v___x_5458_ = l_Lean_Name_str___override(v___x_5457_, v_str_5446_);
v___x_5459_ = l_Lean_Expr_const___override(v___x_5458_, v_us_5445_);
v___x_5460_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5459_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5460_;
goto v___jp_5414_;
}
else
{
lean_object* v___x_5461_; uint8_t v___x_5462_; 
lean_dec_ref(v_str_5448_);
v___x_5461_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_5462_ = lean_string_dec_eq(v_str_5447_, v___x_5461_);
if (v___x_5462_ == 0)
{
lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
lean_dec(v_addDeclName_5410_);
v___x_5463_ = l_Lean_Name_str___override(v_pre_5444_, v___x_5450_);
v___x_5464_ = l_Lean_Name_str___override(v___x_5463_, v___x_5453_);
v___x_5465_ = l_Lean_Name_str___override(v___x_5464_, v_str_5447_);
v___x_5466_ = l_Lean_Name_str___override(v___x_5465_, v_str_5446_);
v___x_5467_ = l_Lean_Expr_const___override(v___x_5466_, v_us_5445_);
v___x_5468_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5467_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5468_;
goto v___jp_5414_;
}
else
{
lean_object* v___x_5469_; uint8_t v___x_5470_; 
lean_dec_ref(v_str_5447_);
v___x_5469_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4));
v___x_5470_ = lean_string_dec_eq(v_str_5446_, v___x_5469_);
if (v___x_5470_ == 0)
{
lean_object* v___x_5471_; uint8_t v___x_5472_; 
v___x_5471_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5));
v___x_5472_ = lean_string_dec_eq(v_str_5446_, v___x_5471_);
if (v___x_5472_ == 0)
{
lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
lean_dec(v_addDeclName_5410_);
v___x_5473_ = l_Lean_Name_str___override(v_pre_5444_, v___x_5450_);
v___x_5474_ = l_Lean_Name_str___override(v___x_5473_, v___x_5453_);
v___x_5475_ = l_Lean_Name_str___override(v___x_5474_, v___x_5461_);
v___x_5476_ = l_Lean_Name_str___override(v___x_5475_, v_str_5446_);
v___x_5477_ = l_Lean_Expr_const___override(v___x_5476_, v_us_5445_);
v___x_5478_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5477_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5478_;
goto v___jp_5414_;
}
else
{
lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
lean_dec_ref(v_str_5446_);
lean_dec(v_us_5445_);
lean_dec_ref(v___f_5438_);
v___x_5479_ = lean_box(0);
v___x_5480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18);
v___x_5481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19);
v___x_5482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20);
lean_inc(v_declName_5408_);
v___x_5483_ = l_Lean_mkConst(v_declName_5408_, v___x_5479_);
v___x_5484_ = l_Lean_mkApp3(v___x_5480_, v___x_5481_, v___x_5482_, v___x_5483_);
v___x_5485_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(v_addDeclName_5410_, v_declName_5408_, v___y_5431_, v___x_5484_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5485_;
goto v___jp_5414_;
}
}
else
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
lean_dec_ref(v_str_5446_);
lean_dec(v_us_5445_);
lean_dec_ref(v___f_5438_);
v___x_5486_ = lean_box(0);
v___x_5487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__23, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__23_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__23);
v___x_5488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19);
v___x_5489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20);
lean_inc(v_declName_5408_);
v___x_5490_ = l_Lean_mkConst(v_declName_5408_, v___x_5486_);
v___x_5491_ = l_Lean_mkApp3(v___x_5487_, v___x_5488_, v___x_5489_, v___x_5490_);
v___x_5492_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(v_addDeclName_5410_, v_declName_5408_, v___y_5431_, v___x_5491_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5492_;
goto v___jp_5414_;
}
}
}
}
}
else
{
lean_object* v___x_5493_; 
lean_dec_ref(v_pre_5443_);
lean_dec(v_pre_5444_);
lean_dec_ref(v_pre_5442_);
lean_dec_ref(v_pre_5441_);
lean_dec_ref(v_declName_5440_);
lean_dec(v_addDeclName_5410_);
v___x_5493_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5493_;
goto v___jp_5414_;
}
}
else
{
lean_object* v___x_5494_; 
lean_dec_ref(v_pre_5442_);
lean_dec(v_pre_5443_);
lean_dec_ref(v_pre_5441_);
lean_dec_ref(v_declName_5440_);
lean_dec(v_addDeclName_5410_);
v___x_5494_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5494_;
goto v___jp_5414_;
}
}
else
{
lean_object* v___x_5495_; 
lean_dec(v_pre_5442_);
lean_dec_ref(v_pre_5441_);
lean_dec_ref(v_declName_5440_);
lean_dec(v_addDeclName_5410_);
v___x_5495_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5495_;
goto v___jp_5414_;
}
}
else
{
lean_object* v___x_5496_; 
lean_dec(v_pre_5441_);
lean_dec_ref(v_declName_5440_);
lean_dec(v_addDeclName_5410_);
v___x_5496_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5496_;
goto v___jp_5414_;
}
}
else
{
lean_object* v___x_5497_; 
lean_dec(v_declName_5440_);
lean_dec(v_addDeclName_5410_);
v___x_5497_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5497_;
goto v___jp_5414_;
}
}
else
{
lean_object* v___x_5498_; 
lean_dec(v_addDeclName_5410_);
v___x_5498_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5408_, v___f_5438_, v___x_5439_, v___x_5432_, v___x_5434_, v_a_5411_, v_a_5412_);
lean_dec_ref(v___f_5438_);
v___y_5415_ = v___x_5434_;
v___y_5416_ = v___x_5498_;
goto v___jp_5414_;
}
}
else
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
lean_dec(v___x_5434_);
lean_dec(v_addDeclName_5410_);
lean_dec(v_declName_5408_);
v_a_5499_ = lean_ctor_get(v___x_5435_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5435_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5501_ = v___x_5435_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5435_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object* v_declName_5512_, lean_object* v_stx_5513_, lean_object* v_addDeclName_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_){
_start:
{
lean_object* v_res_5518_; 
v_res_5518_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(v_declName_5512_, v_stx_5513_, v_addDeclName_5514_, v_a_5515_, v_a_5516_);
lean_dec(v_a_5516_);
lean_dec_ref(v_a_5515_);
lean_dec(v_stx_5513_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0(lean_object* v_00_u03b1_5519_, lean_object* v_msg_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v___x_5526_; 
v___x_5526_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v_msg_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___boxed(lean_object* v_00_u03b1_5527_, lean_object* v_msg_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
lean_object* v_res_5534_; 
v_res_5534_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0(v_00_u03b1_5527_, v_msg_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
lean_dec(v___y_5532_);
lean_dec_ref(v___y_5531_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
return v_res_5534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1(lean_object* v_00_u03b1_5535_, lean_object* v_constName_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_){
_start:
{
lean_object* v___x_5542_; 
v___x_5542_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(v_constName_5536_, v___y_5537_, v___y_5538_, v___y_5539_, v___y_5540_);
return v___x_5542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5543_, lean_object* v_constName_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
lean_object* v_res_5550_; 
v_res_5550_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1(v_00_u03b1_5543_, v_constName_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_);
lean_dec(v___y_5548_);
lean_dec_ref(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec_ref(v___y_5545_);
return v_res_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_5551_, lean_object* v_ref_5552_, lean_object* v_constName_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_){
_start:
{
lean_object* v___x_5559_; 
v___x_5559_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(v_ref_5552_, v_constName_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
return v___x_5559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_5560_, lean_object* v_ref_5561_, lean_object* v_constName_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2(v_00_u03b1_5560_, v_ref_5561_, v_constName_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
lean_dec(v___y_5566_);
lean_dec_ref(v___y_5565_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v_ref_5561_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_5569_, lean_object* v_ref_5570_, lean_object* v_msg_5571_, lean_object* v_declHint_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_){
_start:
{
lean_object* v___x_5578_; 
v___x_5578_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_5570_, v_msg_5571_, v_declHint_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5579_, lean_object* v_ref_5580_, lean_object* v_msg_5581_, lean_object* v_declHint_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_){
_start:
{
lean_object* v_res_5588_; 
v_res_5588_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_5579_, v_ref_5580_, v_msg_5581_, v_declHint_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
lean_dec(v_ref_5580_);
return v_res_5588_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_5589_, lean_object* v_declHint_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v___x_5596_; 
v___x_5596_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5589_, v_declHint_5590_, v___y_5594_);
return v___x_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_5597_, lean_object* v_declHint_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_5597_, v_declHint_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
return v_res_5604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_5605_, lean_object* v_ref_5606_, lean_object* v_msg_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
lean_object* v___x_5613_; 
v___x_5613_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5606_, v_msg_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_);
return v___x_5613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5614_, lean_object* v_ref_5615_, lean_object* v_msg_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v_res_5622_; 
v_res_5622_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_5614_, v_ref_5615_, v_msg_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
lean_dec(v_ref_5615_);
return v_res_5622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5624_; lean_object* v___x_5625_; 
v___x_5624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_));
v___x_5625_ = l_Lean_stringToMessageData(v___x_5624_);
return v___x_5625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(lean_object* v_x_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_){
_start:
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_);
v___x_5631_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_5630_, v___y_5627_, v___y_5628_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object* v_x_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_){
_start:
{
lean_object* v_res_5636_; 
v_res_5636_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(v_x_5632_, v___y_5633_, v___y_5634_);
lean_dec(v___y_5634_);
lean_dec_ref(v___y_5633_);
lean_dec(v_x_5632_);
return v_res_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(lean_object* v___x_5638_, lean_object* v___x_5639_, lean_object* v___x_5640_, lean_object* v_declName_5641_, lean_object* v_stx_5642_, uint8_t v_x_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; 
v___x_5647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_));
v___x_5648_ = l_Lean_Name_mkStr4(v___x_5638_, v___x_5639_, v___x_5640_, v___x_5647_);
v___x_5649_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(v_declName_5641_, v_stx_5642_, v___x_5648_, v___y_5644_, v___y_5645_);
return v___x_5649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object* v___x_5650_, lean_object* v___x_5651_, lean_object* v___x_5652_, lean_object* v_declName_5653_, lean_object* v_stx_5654_, lean_object* v_x_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_){
_start:
{
uint8_t v_x_151__boxed_5659_; lean_object* v_res_5660_; 
v_x_151__boxed_5659_ = lean_unbox(v_x_5655_);
v_res_5660_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(v___x_5650_, v___x_5651_, v___x_5652_, v_declName_5653_, v_stx_5654_, v_x_151__boxed_5659_, v___y_5656_, v___y_5657_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v_stx_5654_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_));
v___x_5749_ = l_Lean_registerBuiltinAttribute(v___x_5748_);
return v___x_5749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object* v_a_5750_){
_start:
{
lean_object* v_res_5751_; 
v_res_5751_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_();
return v_res_5751_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5753_; lean_object* v___x_5754_; 
v___x_5753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_));
v___x_5754_ = l_Lean_stringToMessageData(v___x_5753_);
return v___x_5754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(lean_object* v_x_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_){
_start:
{
lean_object* v___x_5759_; lean_object* v___x_5760_; 
v___x_5759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_);
v___x_5760_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_5759_, v___y_5756_, v___y_5757_);
return v___x_5760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object* v_x_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(v_x_5761_, v___y_5762_, v___y_5763_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec(v_x_5761_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(lean_object* v___x_5767_, lean_object* v___x_5768_, lean_object* v___x_5769_, lean_object* v_declName_5770_, lean_object* v_stx_5771_, uint8_t v_x_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_){
_start:
{
lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; 
v___x_5776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_));
v___x_5777_ = l_Lean_Name_mkStr4(v___x_5767_, v___x_5768_, v___x_5769_, v___x_5776_);
v___x_5778_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(v_declName_5770_, v_stx_5771_, v___x_5777_, v___y_5773_, v___y_5774_);
return v___x_5778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object* v___x_5779_, lean_object* v___x_5780_, lean_object* v___x_5781_, lean_object* v_declName_5782_, lean_object* v_stx_5783_, lean_object* v_x_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
uint8_t v_x_151__boxed_5788_; lean_object* v_res_5789_; 
v_x_151__boxed_5788_ = lean_unbox(v_x_5784_);
v_res_5789_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(v___x_5779_, v___x_5780_, v___x_5781_, v_declName_5782_, v_stx_5783_, v_x_151__boxed_5788_, v___y_5785_, v___y_5786_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5785_);
lean_dec(v_stx_5783_);
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_));
v___x_5822_ = l_Lean_registerBuiltinAttribute(v___x_5821_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object* v_a_5823_){
_start:
{
lean_object* v_res_5824_; 
v_res_5824_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_();
return v_res_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg(lean_object* v_a_5825_){
_start:
{
lean_object* v___x_5827_; lean_object* v_env_5828_; lean_object* v___x_5829_; lean_object* v_ext_5830_; lean_object* v_toEnvExtension_5831_; lean_object* v_asyncMode_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; 
v___x_5827_ = lean_st_ref_get(v_a_5825_);
v_env_5828_ = lean_ctor_get(v___x_5827_, 0);
lean_inc_ref(v_env_5828_);
lean_dec(v___x_5827_);
v___x_5829_ = l_Lean_Meta_Simp_simprocExtension;
v_ext_5830_ = lean_ctor_get(v___x_5829_, 1);
lean_inc_ref(v_ext_5830_);
v_toEnvExtension_5831_ = lean_ctor_get(v_ext_5830_, 0);
lean_inc_ref(v_toEnvExtension_5831_);
lean_dec_ref(v_ext_5830_);
v_asyncMode_5832_ = lean_ctor_get(v_toEnvExtension_5831_, 2);
lean_inc(v_asyncMode_5832_);
lean_dec_ref(v_toEnvExtension_5831_);
v___x_5833_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_5834_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5833_, v___x_5829_, v_env_5828_, v_asyncMode_5832_);
lean_dec(v_asyncMode_5832_);
v___x_5835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5835_, 0, v___x_5834_);
return v___x_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg___boxed(lean_object* v_a_5836_, lean_object* v_a_5837_){
_start:
{
lean_object* v_res_5838_; 
v_res_5838_ = l_Lean_Meta_Simp_getSimprocs___redArg(v_a_5836_);
lean_dec(v_a_5836_);
return v_res_5838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object* v_a_5839_, lean_object* v_a_5840_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = l_Lean_Meta_Simp_getSimprocs___redArg(v_a_5840_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
lean_object* v_res_5846_; 
v_res_5846_ = l_Lean_Meta_Simp_getSimprocs(v_a_5843_, v_a_5844_);
lean_dec(v_a_5844_);
lean_dec_ref(v_a_5843_);
return v_res_5846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object* v_a_5847_){
_start:
{
lean_object* v___x_5849_; lean_object* v_env_5850_; lean_object* v___x_5851_; lean_object* v_ext_5852_; lean_object* v_toEnvExtension_5853_; lean_object* v_asyncMode_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; 
v___x_5849_ = lean_st_ref_get(v_a_5847_);
v_env_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc_ref(v_env_5850_);
lean_dec(v___x_5849_);
v___x_5851_ = l_Lean_Meta_Simp_simprocSEvalExtension;
v_ext_5852_ = lean_ctor_get(v___x_5851_, 1);
lean_inc_ref(v_ext_5852_);
v_toEnvExtension_5853_ = lean_ctor_get(v_ext_5852_, 0);
lean_inc_ref(v_toEnvExtension_5853_);
lean_dec_ref(v_ext_5852_);
v_asyncMode_5854_ = lean_ctor_get(v_toEnvExtension_5853_, 2);
lean_inc(v_asyncMode_5854_);
lean_dec_ref(v_toEnvExtension_5853_);
v___x_5855_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_5856_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5855_, v___x_5851_, v_env_5850_, v_asyncMode_5854_);
lean_dec(v_asyncMode_5854_);
v___x_5857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5857_, 0, v___x_5856_);
return v___x_5857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg___boxed(lean_object* v_a_5858_, lean_object* v_a_5859_){
_start:
{
lean_object* v_res_5860_; 
v_res_5860_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_5858_);
lean_dec(v_a_5858_);
return v_res_5860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object* v_a_5861_, lean_object* v_a_5862_){
_start:
{
lean_object* v___x_5864_; 
v___x_5864_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_5862_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object* v_a_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_){
_start:
{
lean_object* v_res_5868_; 
v_res_5868_ = l_Lean_Meta_Simp_getSEvalSimprocs(v_a_5865_, v_a_5866_);
lean_dec(v_a_5866_);
lean_dec_ref(v_a_5865_);
return v_res_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object* v_attrName_5869_){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5871_ = l_Lean_Meta_Simp_simprocExtensionMapRef;
v___x_5872_ = lean_st_ref_get(v___x_5871_);
v___x_5873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v___x_5872_, v_attrName_5869_);
lean_dec(v___x_5872_);
v___x_5874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5874_, 0, v___x_5873_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object* v_attrName_5875_, lean_object* v_a_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(v_attrName_5875_);
lean_dec(v_attrName_5875_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object* v_attrName_5884_){
_start:
{
lean_object* v___x_5885_; uint8_t v___x_5886_; 
v___x_5885_ = ((lean_object*)(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__0));
v___x_5886_ = lean_name_eq(v_attrName_5884_, v___x_5885_);
if (v___x_5886_ == 0)
{
lean_object* v___x_5887_; uint8_t v___x_5888_; 
v___x_5887_ = ((lean_object*)(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2));
v___x_5888_ = lean_name_eq(v_attrName_5884_, v___x_5887_);
if (v___x_5888_ == 0)
{
lean_object* v___x_5889_; lean_object* v___x_5890_; 
v___x_5889_ = ((lean_object*)(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3));
v___x_5890_ = lean_name_append_after(v_attrName_5884_, v___x_5889_);
return v___x_5890_;
}
else
{
lean_object* v___x_5891_; 
lean_dec(v_attrName_5884_);
v___x_5891_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
return v___x_5891_;
}
}
else
{
lean_object* v___x_5892_; 
lean_dec(v_attrName_5884_);
v___x_5892_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
return v___x_5892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object* v_simprocAttrNameOrsimpAttrName_5893_){
_start:
{
lean_object* v___x_5895_; lean_object* v_a_5896_; 
v___x_5895_ = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(v_simprocAttrNameOrsimpAttrName_5893_);
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
lean_inc(v_a_5896_);
if (lean_obj_tag(v_a_5896_) == 1)
{
lean_dec_ref(v_a_5896_);
lean_dec(v_simprocAttrNameOrsimpAttrName_5893_);
return v___x_5895_;
}
else
{
lean_object* v___x_5897_; lean_object* v___x_5898_; 
lean_dec(v_a_5896_);
lean_dec_ref(v___x_5895_);
v___x_5897_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_simprocAttrNameOrsimpAttrName_5893_);
v___x_5898_ = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(v___x_5897_);
lean_dec(v___x_5897_);
return v___x_5898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f___boxed(lean_object* v_simprocAttrNameOrsimpAttrName_5899_, lean_object* v_a_5900_){
_start:
{
lean_object* v_res_5901_; 
v_res_5901_ = l_Lean_Meta_Simp_getSimprocExtension_x3f(v_simprocAttrNameOrsimpAttrName_5899_);
return v_res_5901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object* v_ext_5902_, lean_object* v_a_5903_){
_start:
{
lean_object* v___x_5905_; lean_object* v_ext_5906_; lean_object* v_toEnvExtension_5907_; lean_object* v_env_5908_; lean_object* v_asyncMode_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
v___x_5905_ = lean_st_ref_get(v_a_5903_);
v_ext_5906_ = lean_ctor_get(v_ext_5902_, 1);
v_toEnvExtension_5907_ = lean_ctor_get(v_ext_5906_, 0);
v_env_5908_ = lean_ctor_get(v___x_5905_, 0);
lean_inc_ref(v_env_5908_);
lean_dec(v___x_5905_);
v_asyncMode_5909_ = lean_ctor_get(v_toEnvExtension_5907_, 2);
v___x_5910_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_5911_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5910_, v_ext_5902_, v_env_5908_, v_asyncMode_5909_);
v___x_5912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5911_);
return v___x_5912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg___boxed(lean_object* v_ext_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_){
_start:
{
lean_object* v_res_5916_; 
v_res_5916_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(v_ext_5913_, v_a_5914_);
lean_dec(v_a_5914_);
lean_dec_ref(v_ext_5913_);
return v_res_5916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object* v_ext_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_){
_start:
{
lean_object* v___x_5921_; 
v___x_5921_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(v_ext_5917_, v_a_5919_);
return v___x_5921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object* v_ext_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_){
_start:
{
lean_object* v_res_5926_; 
v_res_5926_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(v_ext_5922_, v_a_5923_, v_a_5924_);
lean_dec(v_a_5924_);
lean_dec_ref(v_a_5923_);
lean_dec_ref(v_ext_5922_);
return v_res_5926_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default = _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default);
l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs = _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1481072680____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSimprocDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSimprocDeclsRef);
lean_dec_ref(res);
l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default = _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState_default);
l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState = _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocDeclExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocDeclExt);
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSimprocsRef);
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1207380286____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSEvalprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSEvalprocsRef);
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocs);
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocExtensionMapRef);
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocExtension);
lean_dec_ref(res);
res = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocSEvalExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocSEvalExtension);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Meta_Simp_mkSimprocExt___auto__1 = _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSimprocExt___auto__1);
l_Lean_Meta_Simp_registerSimprocAttr___auto__1 = _init_l_Lean_Meta_Simp_registerSimprocAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Simp_registerSimprocAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
}
#ifdef __cplusplus
}
#endif
