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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
lean_object* l_Lean_instToExprName___private__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2;
static const lean_array_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inr"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 118, 236, 113, 107, 136, 194, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__9_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__18_value),LEAN_SCALAR_PTR_LITERAL(236, 33, 85, 75, 207, 191, 2, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20;
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
size_t v_x_1770__boxed_193_; size_t v_x_1771__boxed_194_; lean_object* v_res_195_; 
v_x_1770__boxed_193_ = lean_unbox_usize(v_x_189_);
lean_dec(v_x_189_);
v_x_1771__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_188_, v_x_1770__boxed_193_, v_x_1771__boxed_194_, v_x_191_, v_x_192_);
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
uint8_t v_x_2125__boxed_370_; lean_object* v_res_371_; 
v_x_2125__boxed_370_ = lean_unbox(v_x_369_);
v_res_371_ = l_Lean_Meta_Simp_initFn___lam__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_(v___f_366_, v_x_367_, v_s_368_, v_x_2125__boxed_370_);
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
size_t v_x_2342__boxed_493_; size_t v_x_2343__boxed_494_; lean_object* v_res_495_; 
v_x_2342__boxed_493_ = lean_unbox_usize(v_x_489_);
lean_dec(v_x_489_);
v_x_2343__boxed_494_ = lean_unbox_usize(v_x_490_);
lean_dec(v_x_490_);
v_res_495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_487_, v_x_488_, v_x_2342__boxed_493_, v_x_2343__boxed_494_, v_x_491_, v_x_492_);
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
size_t v_x_2007__boxed_712_; lean_object* v_res_713_; 
v_x_2007__boxed_712_ = lean_unbox_usize(v_x_710_);
lean_dec(v_x_710_);
v_res_713_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_709_, v_x_2007__boxed_712_, v_x_711_);
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
size_t v_x_2221__boxed_839_; lean_object* v_res_840_; 
v_x_2221__boxed_839_ = lean_unbox_usize(v_x_837_);
lean_dec(v_x_837_);
v_res_840_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_835_, v_x_836_, v_x_2221__boxed_839_, v_x_838_);
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
lean_dec_ref(v_opts_1593_);
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
lean_dec_ref(v_opts_1593_);
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
lean_dec(v_pre_1629_);
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
lean_dec_ref(v_declName_1626_);
lean_dec(v_pre_1627_);
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
size_t v_x_556__boxed_1754_; uint8_t v_res_1755_; lean_object* v_r_1756_; 
v_x_556__boxed_1754_ = lean_unbox_usize(v_x_1752_);
lean_dec(v_x_1752_);
v_res_1755_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0___redArg(v_x_1751_, v_x_556__boxed_1754_, v_x_1753_);
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
size_t v_x_729__boxed_1851_; uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_x_729__boxed_1851_ = lean_unbox_usize(v_x_1849_);
lean_dec(v_x_1849_);
v_res_1852_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0_spec__0(v_00_u03b2_1847_, v_x_1848_, v_x_729__boxed_1851_, v_x_1850_);
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
lean_dec_ref(v_a_1937_);
return v___x_1959_;
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1971_; 
lean_inc(v_ref_1943_);
lean_dec_ref(v_a_1937_);
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
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
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
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
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
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec_ref(v_a_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
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
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
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
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
lean_inc_ref(v___y_3044_);
lean_inc(v___y_3043_);
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
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
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
lean_dec(v___y_3114_);
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
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
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
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
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
lean_dec(v___y_3192_);
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
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
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
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
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
lean_inc(v___y_3049_);
lean_inc_ref(v___y_3048_);
lean_inc(v___y_3047_);
lean_inc_ref(v___y_3046_);
lean_inc(v___y_3045_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_dec(v___y_3274_);
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
v___y_3087_ = v_a_3286_;
v___y_3088_ = v_expr_3281_;
v___y_3089_ = v___x_3108_;
goto v___jp_3086_;
}
else
{
lean_object* v_a_3287_; 
v_a_3287_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3287_);
lean_dec_ref(v___x_3284_);
v___y_3087_ = v_a_3287_;
v___y_3088_ = v_expr_3281_;
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v_val_3272_);
lean_del_object(v___x_3082_);
lean_dec(v_snd_3080_);
lean_del_object(v___x_3077_);
lean_dec(v_fst_3075_);
lean_del_object(v___x_3073_);
lean_del_object(v___x_3061_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
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
lean_ctor_set(v___x_3077_, 0, v___y_3087_);
v___x_3095_ = v___x_3077_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___y_3087_);
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
lean_ctor_set(v___x_3073_, 0, v___y_3088_);
v___x_3097_ = v___x_3073_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___y_3088_);
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
lean_object* v___y_3411_; lean_object* v_a_3433_; lean_object* v_indexConfig_3487_; lean_object* v_config_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3518_; 
v_indexConfig_3487_ = lean_ctor_get(v_a_3400_, 4);
lean_inc_ref(v_indexConfig_3487_);
v_config_3488_ = lean_ctor_get(v_indexConfig_3487_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_indexConfig_3487_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3490_ = v_indexConfig_3487_;
v_isShared_3491_ = v_isSharedCheck_3518_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_config_3488_);
lean_dec(v_indexConfig_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3518_;
goto v_resetjp_3489_;
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
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
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
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
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
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
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
v_resetjp_3489_:
{
uint8_t v_trackZetaDelta_3492_; lean_object* v_zetaDeltaSet_3493_; lean_object* v_lctx_3494_; lean_object* v_localInstances_3495_; lean_object* v_defEqCtx_x3f_3496_; lean_object* v_synthPendingDepth_3497_; lean_object* v_canUnfold_x3f_3498_; uint8_t v_univApprox_3499_; uint8_t v_inTypeClassResolution_3500_; uint8_t v_cacheInferType_3501_; uint64_t v___x_3502_; lean_object* v___x_3504_; 
v_trackZetaDelta_3492_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7);
v_zetaDeltaSet_3493_ = lean_ctor_get(v_a_3402_, 1);
v_lctx_3494_ = lean_ctor_get(v_a_3402_, 2);
v_localInstances_3495_ = lean_ctor_get(v_a_3402_, 3);
v_defEqCtx_x3f_3496_ = lean_ctor_get(v_a_3402_, 4);
v_synthPendingDepth_3497_ = lean_ctor_get(v_a_3402_, 5);
v_canUnfold_x3f_3498_ = lean_ctor_get(v_a_3402_, 6);
v_univApprox_3499_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3500_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7 + 2);
v_cacheInferType_3501_ = lean_ctor_get_uint8(v_a_3402_, sizeof(void*)*7 + 3);
v___x_3502_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3488_);
if (v_isShared_3491_ == 0)
{
v___x_3504_ = v___x_3490_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_config_3488_);
v___x_3504_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
lean_ctor_set_uint64(v___x_3504_, sizeof(void*)*1, v___x_3502_);
lean_inc(v_canUnfold_x3f_3498_);
lean_inc(v_synthPendingDepth_3497_);
lean_inc(v_defEqCtx_x3f_3496_);
lean_inc_ref(v_localInstances_3495_);
lean_inc_ref(v_lctx_3494_);
lean_inc(v_zetaDeltaSet_3493_);
v___x_3505_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
lean_ctor_set(v___x_3505_, 1, v_zetaDeltaSet_3493_);
lean_ctor_set(v___x_3505_, 2, v_lctx_3494_);
lean_ctor_set(v___x_3505_, 3, v_localInstances_3495_);
lean_ctor_set(v___x_3505_, 4, v_defEqCtx_x3f_3496_);
lean_ctor_set(v___x_3505_, 5, v_synthPendingDepth_3497_);
lean_ctor_set(v___x_3505_, 6, v_canUnfold_x3f_3498_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*7, v_trackZetaDelta_3492_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*7 + 1, v_univApprox_3499_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3500_);
lean_ctor_set_uint8(v___x_3505_, sizeof(void*)*7 + 3, v_cacheInferType_3501_);
lean_inc(v_a_3405_);
lean_inc_ref(v_a_3404_);
lean_inc(v_a_3403_);
lean_inc_ref(v_e_3398_);
v___x_3506_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_s_3396_, v_e_3398_, v___x_3505_, v_a_3403_, v_a_3404_, v_a_3405_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref(v___x_3506_);
v_a_3433_ = v_a_3507_;
goto v___jp_3432_;
}
else
{
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3508_; 
v_a_3508_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3508_);
lean_dec_ref(v___x_3506_);
v_a_3433_ = v_a_3508_;
goto v___jp_3432_;
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_e_3398_);
lean_dec_ref(v_erased_3397_);
v_a_3509_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3506_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3506_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object* v_post_3519_, lean_object* v_s_3520_, lean_object* v_erased_3521_, lean_object* v_e_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
uint8_t v_post_boxed_3531_; lean_object* v_res_3532_; 
v_post_boxed_3531_ = lean_unbox(v_post_3519_);
v_res_3532_ = l_Lean_Meta_Simp_simprocCore(v_post_boxed_3531_, v_s_3520_, v_erased_3521_, v_e_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1(lean_object* v_cls_3533_, lean_object* v_msg_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v_cls_3533_, v_msg_3534_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___boxed(lean_object* v_cls_3544_, lean_object* v_msg_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1(v_cls_3544_, v_msg_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(lean_object* v_erased_3555_, uint8_t v_post_3556_, lean_object* v___x_3557_, lean_object* v_as_3558_, size_t v_sz_3559_, size_t v_i_3560_, lean_object* v_b_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_a_3571_; uint8_t v___x_3575_; 
v___x_3575_ = lean_usize_dec_lt(v_i_3560_, v_sz_3559_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; 
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v_b_3561_);
return v___x_3576_;
}
else
{
lean_object* v_a_3577_; lean_object* v_snd_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3780_; 
v_a_3577_ = lean_array_uget(v_as_3558_, v_i_3560_);
v_snd_3578_ = lean_ctor_get(v_b_3561_, 1);
v_isSharedCheck_3780_ = !lean_is_exclusive(v_b_3561_);
if (v_isSharedCheck_3780_ == 0)
{
lean_object* v_unused_3781_; 
v_unused_3781_ = lean_ctor_get(v_b_3561_, 0);
lean_dec(v_unused_3781_);
v___x_3580_ = v_b_3561_;
v_isShared_3581_ = v_isSharedCheck_3780_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_snd_3578_);
lean_dec(v_b_3561_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3780_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_fst_3582_; lean_object* v_toSimprocOLeanEntry_3583_; lean_object* v_snd_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3778_; 
v_fst_3582_ = lean_ctor_get(v_a_3577_, 0);
lean_inc(v_fst_3582_);
v_toSimprocOLeanEntry_3583_ = lean_ctor_get(v_fst_3582_, 0);
v_snd_3584_ = lean_ctor_get(v_a_3577_, 1);
v_isSharedCheck_3778_ = !lean_is_exclusive(v_a_3577_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; 
v_unused_3779_ = lean_ctor_get(v_a_3577_, 0);
lean_dec(v_unused_3779_);
v___x_3586_ = v_a_3577_;
v_isShared_3587_ = v_isSharedCheck_3778_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snd_3584_);
lean_dec(v_a_3577_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3778_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v_fst_3588_; lean_object* v_snd_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3777_; 
v_fst_3588_ = lean_ctor_get(v_snd_3578_, 0);
v_snd_3589_ = lean_ctor_get(v_snd_3578_, 1);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_snd_3578_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3591_ = v_snd_3578_;
v_isShared_3592_ = v_isSharedCheck_3777_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_snd_3589_);
lean_inc(v_fst_3588_);
lean_dec(v_snd_3578_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3777_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_declName_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v_declName_3593_ = lean_ctor_get(v_toSimprocOLeanEntry_3583_, 0);
lean_inc(v_declName_3593_);
v___x_3594_ = lean_box(0);
lean_inc_ref(v_erased_3555_);
v___x_3595_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_erased_3555_, v_declName_3593_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; 
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3566_);
lean_inc_ref(v___y_3565_);
lean_inc(v___y_3564_);
lean_inc_ref(v___y_3563_);
lean_inc(v___y_3562_);
lean_inc(v_fst_3588_);
v___x_3596_ = l_Lean_Meta_Simp_SimprocEntry_tryD(v_fst_3582_, v_snd_3584_, v_fst_3588_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v_snd_3584_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref(v___x_3596_);
v___x_3598_ = lean_unsigned_to_nat(0u);
v___x_3599_ = lean_nat_dec_eq(v___x_3557_, v___x_3598_);
switch(lean_obj_tag(v_a_3597_))
{
case 0:
{
lean_object* v_e_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
lean_del_object(v___x_3586_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v_e_3656_ = lean_ctor_get(v_a_3597_, 0);
v___x_3657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3658_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3657_, v___y_3567_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; uint8_t v___x_3660_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref(v___x_3658_);
v___x_3660_ = lean_unbox(v_a_3659_);
lean_dec(v_a_3659_);
if (v___x_3660_ == 0)
{
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
v___y_3601_ = v___y_3564_;
v___y_3602_ = v___y_3567_;
v___y_3603_ = v___y_3568_;
goto v___jp_3600_;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3661_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
lean_inc(v_fst_3588_);
v___x_3662_ = l_Lean_MessageData_ofExpr(v_fst_3588_);
v___x_3663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3661_);
lean_ctor_set(v___x_3663_, 1, v___x_3662_);
v___x_3664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3663_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
lean_inc_ref(v_e_3656_);
v___x_3666_ = l_Lean_MessageData_ofExpr(v_e_3656_);
v___x_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3665_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3657_, v___x_3667_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_dec_ref(v___x_3668_);
v___y_3601_ = v___y_3564_;
v___y_3602_ = v___y_3567_;
v___y_3603_ = v___y_3568_;
goto v___jp_3600_;
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_dec_ref(v_a_3597_);
lean_dec(v_declName_3593_);
lean_del_object(v___x_3591_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3580_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3564_);
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v_a_3597_);
lean_dec(v_declName_3593_);
lean_del_object(v___x_3591_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3580_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
v_a_3677_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3658_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3658_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
case 1:
{
lean_object* v_e_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
lean_del_object(v___x_3591_);
lean_del_object(v___x_3580_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v_e_3685_ = lean_ctor_get(v_a_3597_, 0);
v___x_3686_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3687_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3686_, v___y_3567_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; uint8_t v___x_3689_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref(v___x_3687_);
v___x_3689_ = lean_unbox(v_a_3688_);
lean_dec(v_a_3688_);
if (v___x_3689_ == 0)
{
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
v___y_3630_ = v___y_3564_;
v___y_3631_ = v___y_3567_;
v___y_3632_ = v___y_3568_;
goto v___jp_3629_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3690_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
lean_inc(v_fst_3588_);
v___x_3691_ = l_Lean_MessageData_ofExpr(v_fst_3588_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
lean_inc_ref(v_e_3685_);
v___x_3695_ = l_Lean_MessageData_ofExpr(v_e_3685_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3686_, v___x_3696_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_dec_ref(v___x_3697_);
v___y_3630_ = v___y_3564_;
v___y_3631_ = v___y_3567_;
v___y_3632_ = v___y_3568_;
goto v___jp_3629_;
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec_ref(v_a_3597_);
lean_dec(v_declName_3593_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3586_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3564_);
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3697_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_a_3597_);
lean_dec(v_declName_3593_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3586_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
v_a_3706_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3687_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3687_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
default: 
{
lean_object* v_e_x3f_3714_; 
lean_del_object(v___x_3591_);
lean_del_object(v___x_3586_);
lean_del_object(v___x_3580_);
v_e_x3f_3714_ = lean_ctor_get(v_a_3597_, 0);
lean_inc(v_e_x3f_3714_);
lean_dec_ref(v_a_3597_);
if (lean_obj_tag(v_e_x3f_3714_) == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_dec(v_declName_3593_);
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_fst_3588_);
lean_ctor_set(v___x_3715_, 1, v_snd_3589_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3594_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v_a_3571_ = v___x_3716_;
goto v___jp_3570_;
}
else
{
lean_object* v_val_3717_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
lean_dec(v_snd_3589_);
v_val_3717_ = lean_ctor_get(v_e_x3f_3714_, 0);
lean_inc(v_val_3717_);
lean_dec_ref(v_e_x3f_3714_);
v___x_3735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3736_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3735_, v___y_3567_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; uint8_t v___x_3738_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
lean_inc(v_a_3737_);
lean_dec_ref(v___x_3736_);
v___x_3738_ = lean_unbox(v_a_3737_);
lean_dec(v_a_3737_);
if (v___x_3738_ == 0)
{
lean_dec(v_fst_3588_);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3564_);
v___y_3719_ = v___y_3564_;
v___y_3720_ = v___y_3567_;
v___y_3721_ = v___y_3568_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3739_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__5);
v___x_3740_ = l_Lean_MessageData_ofExpr(v_fst_3588_);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__7);
v___x_3743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
lean_inc(v_val_3717_);
v___x_3744_ = l_Lean_MessageData_ofExpr(v_val_3717_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3743_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3735_, v___x_3745_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_dec_ref(v___x_3746_);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3564_);
v___y_3719_ = v___y_3564_;
v___y_3720_ = v___y_3567_;
v___y_3721_ = v___y_3568_;
goto v___jp_3718_;
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_val_3717_);
lean_dec(v_declName_3593_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3746_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v_val_3717_);
lean_dec(v_declName_3593_);
lean_dec(v_fst_3588_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v_a_3755_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3736_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3736_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
v___jp_3718_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3722_, 0, v_declName_3593_);
lean_ctor_set_uint8(v___x_3722_, sizeof(void*)*1, v_post_3556_);
lean_ctor_set_uint8(v___x_3722_, sizeof(void*)*1 + 1, v___x_3599_);
v___x_3723_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3722_, v___y_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
lean_dec_ref(v___x_3723_);
v___x_3724_ = lean_box(v___x_3575_);
v___x_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3725_, 0, v_val_3717_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3594_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v_a_3571_ = v___x_3726_;
goto v___jp_3570_;
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_val_3717_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v_a_3727_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3723_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3723_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
}
v___jp_3600_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3604_, 0, v_declName_3593_);
lean_ctor_set_uint8(v___x_3604_, sizeof(void*)*1, v_post_3556_);
lean_ctor_set_uint8(v___x_3604_, sizeof(void*)*1 + 1, v___x_3599_);
v___x_3605_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3604_, v___y_3601_, v___y_3602_, v___y_3603_);
lean_dec(v___y_3603_);
lean_dec_ref(v___y_3602_);
lean_dec(v___y_3601_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3619_; 
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v___x_3605_, 0);
lean_dec(v_unused_3620_);
v___x_3607_ = v___x_3605_;
v_isShared_3608_ = v_isSharedCheck_3619_;
goto v_resetjp_3606_;
}
else
{
lean_dec(v___x_3605_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3619_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v_a_3597_);
if (v_isShared_3592_ == 0)
{
v___x_3611_ = v___x_3591_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_fst_3588_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_snd_3589_);
v___x_3611_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v___x_3611_);
lean_ctor_set(v___x_3580_, 0, v___x_3609_);
v___x_3613_ = v___x_3580_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3613_);
v___x_3615_ = v___x_3607_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_a_3597_);
lean_del_object(v___x_3591_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3580_);
v_a_3621_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3605_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3605_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
v___jp_3629_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_3633_, 0, v_declName_3593_);
lean_ctor_set_uint8(v___x_3633_, sizeof(void*)*1, v_post_3556_);
lean_ctor_set_uint8(v___x_3633_, sizeof(void*)*1 + 1, v___x_3599_);
v___x_3634_ = l_Lean_Meta_Simp_recordSimpTheorem___redArg(v___x_3633_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3646_; 
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; 
v_unused_3647_ = lean_ctor_get(v___x_3634_, 0);
lean_dec(v_unused_3647_);
v___x_3636_ = v___x_3634_;
v_isShared_3637_ = v_isSharedCheck_3646_;
goto v_resetjp_3635_;
}
else
{
lean_dec(v___x_3634_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3646_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; lean_object* v___x_3640_; 
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_a_3597_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v_snd_3589_);
lean_ctor_set(v___x_3586_, 0, v_fst_3588_);
v___x_3640_ = v___x_3586_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_fst_3588_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_snd_3589_);
v___x_3640_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3638_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3641_);
v___x_3643_ = v___x_3636_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v_a_3597_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3586_);
v_a_3648_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3634_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3634_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3770_; 
lean_dec(v_declName_3593_);
lean_del_object(v___x_3591_);
lean_dec(v_snd_3589_);
lean_dec(v_fst_3588_);
lean_del_object(v___x_3586_);
lean_del_object(v___x_3580_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v_erased_3555_);
v_a_3763_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3765_ = v___x_3596_;
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3596_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3770_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3768_; 
if (v_isShared_3766_ == 0)
{
v___x_3768_ = v___x_3765_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
}
else
{
lean_object* v___x_3772_; 
lean_dec(v_declName_3593_);
lean_del_object(v___x_3586_);
lean_dec(v_snd_3584_);
lean_dec(v_fst_3582_);
if (v_isShared_3592_ == 0)
{
v___x_3772_ = v___x_3591_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_fst_3588_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_snd_3589_);
v___x_3772_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3774_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v___x_3772_);
lean_ctor_set(v___x_3580_, 0, v___x_3594_);
v___x_3774_ = v___x_3580_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
v_a_3571_ = v___x_3774_;
goto v___jp_3570_;
}
}
}
}
}
}
}
v___jp_3570_:
{
size_t v___x_3572_; size_t v___x_3573_; 
v___x_3572_ = ((size_t)1ULL);
v___x_3573_ = lean_usize_add(v_i_3560_, v___x_3572_);
v_i_3560_ = v___x_3573_;
v_b_3561_ = v_a_3571_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0___boxed(lean_object* v_erased_3782_, lean_object* v_post_3783_, lean_object* v___x_3784_, lean_object* v_as_3785_, lean_object* v_sz_3786_, lean_object* v_i_3787_, lean_object* v_b_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
uint8_t v_post_boxed_3797_; size_t v_sz_boxed_3798_; size_t v_i_boxed_3799_; lean_object* v_res_3800_; 
v_post_boxed_3797_ = lean_unbox(v_post_3783_);
v_sz_boxed_3798_ = lean_unbox_usize(v_sz_3786_);
lean_dec(v_sz_3786_);
v_i_boxed_3799_ = lean_unbox_usize(v_i_3787_);
lean_dec(v_i_3787_);
v_res_3800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(v_erased_3782_, v_post_boxed_3797_, v___x_3784_, v_as_3785_, v_sz_boxed_3798_, v_i_boxed_3799_, v_b_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec_ref(v_as_3785_);
lean_dec(v___x_3784_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t v_post_3803_, lean_object* v_s_3804_, lean_object* v_erased_3805_, lean_object* v_e_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_){
_start:
{
lean_object* v___y_3819_; lean_object* v_a_3841_; lean_object* v_indexConfig_3885_; lean_object* v_config_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3916_; 
v_indexConfig_3885_ = lean_ctor_get(v_a_3808_, 4);
lean_inc_ref(v_indexConfig_3885_);
v_config_3886_ = lean_ctor_get(v_indexConfig_3885_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_indexConfig_3885_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3888_ = v_indexConfig_3885_;
v_isShared_3889_ = v_isSharedCheck_3916_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_config_3886_);
lean_dec(v_indexConfig_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3916_;
goto v_resetjp_3887_;
}
v___jp_3815_:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
v___x_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
return v___x_3817_;
}
v___jp_3818_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v_a_3822_; uint8_t v___x_3823_; 
v___x_3820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocCore_spec__2___closed__3));
v___x_3821_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Simp_simprocCore_spec__0___redArg(v___x_3820_, v_a_3812_);
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = lean_unbox(v_a_3822_);
lean_dec(v_a_3822_);
if (v___x_3823_ == 0)
{
lean_dec_ref(v___y_3819_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec_ref(v_e_3806_);
goto v___jp_3815_;
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3824_ = lean_obj_once(&l_Lean_Meta_Simp_simprocCore___closed__2, &l_Lean_Meta_Simp_simprocCore___closed__2_once, _init_l_Lean_Meta_Simp_simprocCore___closed__2);
v___x_3825_ = l_Lean_stringToMessageData(v___y_3819_);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = lean_obj_once(&l_Lean_Meta_Simp_simprocCore___closed__4, &l_Lean_Meta_Simp_simprocCore___closed__4_once, _init_l_Lean_Meta_Simp_simprocCore___closed__4);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = l_Lean_MessageData_ofExpr(v_e_3806_);
v___x_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = l_Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1___redArg(v___x_3820_, v___x_3830_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_dec_ref(v___x_3831_);
goto v___jp_3815_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
v___jp_3840_:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3842_ = lean_array_get_size(v_a_3841_);
v___x_3843_ = lean_unsigned_to_nat(0u);
v___x_3844_ = lean_nat_dec_eq(v___x_3842_, v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; size_t v_sz_3849_; size_t v___x_3850_; lean_object* v___x_3851_; 
v___x_3845_ = lean_box(0);
v___x_3846_ = lean_box(v___x_3844_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_e_3806_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3845_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v_sz_3849_ = lean_array_size(v_a_3841_);
v___x_3850_ = ((size_t)0ULL);
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocCore_spec__0(v_erased_3805_, v_post_3803_, v___x_3842_, v_a_3841_, v_sz_3849_, v___x_3850_, v___x_3848_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
lean_dec_ref(v_a_3841_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3874_; 
v_a_3852_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3854_ = v___x_3851_;
v_isShared_3855_ = v_isSharedCheck_3874_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3851_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3874_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v_fst_3856_; 
v_fst_3856_ = lean_ctor_get(v_a_3852_, 0);
if (lean_obj_tag(v_fst_3856_) == 0)
{
lean_object* v_snd_3857_; lean_object* v_snd_3858_; uint8_t v___x_3859_; 
v_snd_3857_ = lean_ctor_get(v_a_3852_, 1);
lean_inc(v_snd_3857_);
lean_dec(v_a_3852_);
v_snd_3858_ = lean_ctor_get(v_snd_3857_, 1);
v___x_3859_ = lean_unbox(v_snd_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_dec(v_snd_3857_);
v___x_3860_ = ((lean_object*)(l_Lean_Meta_Simp_dsimprocCore___closed__0));
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3860_);
v___x_3862_ = v___x_3854_;
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
else
{
lean_object* v_fst_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
v_fst_3864_ = lean_ctor_get(v_snd_3857_, 0);
lean_inc(v_fst_3864_);
lean_dec(v_snd_3857_);
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_fst_3864_);
v___x_3866_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3865_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v___x_3866_);
v___x_3868_ = v___x_3854_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
else
{
lean_object* v_val_3870_; lean_object* v___x_3872_; 
lean_inc_ref(v_fst_3856_);
lean_dec(v_a_3852_);
v_val_3870_ = lean_ctor_get(v_fst_3856_, 0);
lean_inc(v_val_3870_);
lean_dec_ref(v_fst_3856_);
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 0, v_val_3870_);
v___x_3872_ = v___x_3854_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_val_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
v_a_3875_ = lean_ctor_get(v___x_3851_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3851_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3851_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
else
{
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_erased_3805_);
if (v_post_3803_ == 0)
{
lean_object* v___x_3883_; 
v___x_3883_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__6));
v___y_3819_ = v___x_3883_;
goto v___jp_3818_;
}
else
{
lean_object* v___x_3884_; 
v___x_3884_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__7));
v___y_3819_ = v___x_3884_;
goto v___jp_3818_;
}
}
}
v_resetjp_3887_:
{
uint8_t v_trackZetaDelta_3890_; lean_object* v_zetaDeltaSet_3891_; lean_object* v_lctx_3892_; lean_object* v_localInstances_3893_; lean_object* v_defEqCtx_x3f_3894_; lean_object* v_synthPendingDepth_3895_; lean_object* v_canUnfold_x3f_3896_; uint8_t v_univApprox_3897_; uint8_t v_inTypeClassResolution_3898_; uint8_t v_cacheInferType_3899_; uint64_t v___x_3900_; lean_object* v___x_3902_; 
v_trackZetaDelta_3890_ = lean_ctor_get_uint8(v_a_3810_, sizeof(void*)*7);
v_zetaDeltaSet_3891_ = lean_ctor_get(v_a_3810_, 1);
v_lctx_3892_ = lean_ctor_get(v_a_3810_, 2);
v_localInstances_3893_ = lean_ctor_get(v_a_3810_, 3);
v_defEqCtx_x3f_3894_ = lean_ctor_get(v_a_3810_, 4);
v_synthPendingDepth_3895_ = lean_ctor_get(v_a_3810_, 5);
v_canUnfold_x3f_3896_ = lean_ctor_get(v_a_3810_, 6);
v_univApprox_3897_ = lean_ctor_get_uint8(v_a_3810_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3898_ = lean_ctor_get_uint8(v_a_3810_, sizeof(void*)*7 + 2);
v_cacheInferType_3899_ = lean_ctor_get_uint8(v_a_3810_, sizeof(void*)*7 + 3);
v___x_3900_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3886_);
if (v_isShared_3889_ == 0)
{
v___x_3902_ = v___x_3888_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_config_3886_);
v___x_3902_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_ctor_set_uint64(v___x_3902_, sizeof(void*)*1, v___x_3900_);
lean_inc(v_canUnfold_x3f_3896_);
lean_inc(v_synthPendingDepth_3895_);
lean_inc(v_defEqCtx_x3f_3894_);
lean_inc_ref(v_localInstances_3893_);
lean_inc_ref(v_lctx_3892_);
lean_inc(v_zetaDeltaSet_3891_);
v___x_3903_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v_zetaDeltaSet_3891_);
lean_ctor_set(v___x_3903_, 2, v_lctx_3892_);
lean_ctor_set(v___x_3903_, 3, v_localInstances_3893_);
lean_ctor_set(v___x_3903_, 4, v_defEqCtx_x3f_3894_);
lean_ctor_set(v___x_3903_, 5, v_synthPendingDepth_3895_);
lean_ctor_set(v___x_3903_, 6, v_canUnfold_x3f_3896_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*7, v_trackZetaDelta_3890_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*7 + 1, v_univApprox_3897_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3898_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*7 + 3, v_cacheInferType_3899_);
lean_inc(v_a_3813_);
lean_inc_ref(v_a_3812_);
lean_inc(v_a_3811_);
lean_inc_ref(v_e_3806_);
v___x_3904_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(v_s_3804_, v_e_3806_, v___x_3903_, v_a_3811_, v_a_3812_, v_a_3813_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref(v___x_3904_);
v_a_3841_ = v_a_3905_;
goto v___jp_3840_;
}
else
{
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3906_; 
v_a_3906_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___x_3904_);
v_a_3841_ = v_a_3906_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_e_3806_);
lean_dec_ref(v_erased_3805_);
v_a_3907_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3904_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3904_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object* v_post_3917_, lean_object* v_s_3918_, lean_object* v_erased_3919_, lean_object* v_e_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
uint8_t v_post_boxed_3929_; lean_object* v_res_3930_; 
v_post_boxed_3929_ = lean_unbox(v_post_3917_);
v_res_3930_ = l_Lean_Meta_Simp_dsimprocCore(v_post_boxed_3929_, v_s_3918_, v_erased_3919_, v_e_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object* v_ss_3931_, lean_object* v_declName_3932_, uint8_t v_post_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v___x_3937_ = lean_array_get_size(v_ss_3931_);
v___x_3938_ = lean_unsigned_to_nat(0u);
v___x_3939_ = lean_nat_dec_eq(v___x_3937_, v___x_3938_);
if (v___x_3939_ == 0)
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_nat_dec_lt(v___x_3938_, v___x_3937_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; 
lean_dec(v_declName_3932_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_ss_3931_);
return v___x_3941_;
}
else
{
lean_object* v_v_3942_; lean_object* v___x_3943_; 
v_v_3942_ = lean_array_fget_borrowed(v_ss_3931_, v___x_3938_);
lean_inc(v_v_3942_);
v___x_3943_ = l_Lean_Meta_Simp_Simprocs_add(v_v_3942_, v_declName_3932_, v_post_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3954_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3946_ = v___x_3943_;
v_isShared_3947_ = v_isSharedCheck_3954_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_a_3944_);
lean_dec(v___x_3943_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3954_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v_xs_x27_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
v___x_3948_ = lean_box(0);
v_xs_x27_3949_ = lean_array_fset(v_ss_3931_, v___x_3938_, v___x_3948_);
v___x_3950_ = lean_array_fset(v_xs_x27_3949_, v___x_3938_, v_a_3944_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 0, v___x_3950_);
v___x_3952_ = v___x_3946_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_ss_3931_);
v_a_3955_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3943_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3943_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
else
{
lean_object* v_s_3963_; lean_object* v___x_3964_; 
lean_dec_ref(v_ss_3931_);
v_s_3963_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_3964_ = l_Lean_Meta_Simp_Simprocs_add(v_s_3963_, v_declName_3932_, v_post_3933_, v_a_3934_, v_a_3935_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3975_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3967_ = v___x_3964_;
v_isShared_3968_ = v_isSharedCheck_3975_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3964_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3975_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_mk_empty_array_with_capacity(v___x_3969_);
v___x_3971_ = lean_array_push(v___x_3970_, v_a_3965_);
if (v_isShared_3968_ == 0)
{
lean_ctor_set(v___x_3967_, 0, v___x_3971_);
v___x_3973_ = v___x_3967_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
else
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3983_; 
v_a_3976_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3978_ = v___x_3964_;
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3964_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3983_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3981_; 
if (v_isShared_3979_ == 0)
{
v___x_3981_ = v___x_3978_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object* v_ss_3984_, lean_object* v_declName_3985_, lean_object* v_post_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
uint8_t v_post_boxed_3990_; lean_object* v_res_3991_; 
v_post_boxed_3990_ = lean_unbox(v_post_3986_);
v_res_3991_ = l_Lean_Meta_Simp_SimprocsArray_add(v_ss_3984_, v_declName_3985_, v_post_boxed_3990_, v_a_3987_, v_a_3988_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(lean_object* v_declName_3992_, size_t v_sz_3993_, size_t v_i_3994_, lean_object* v_bs_3995_){
_start:
{
uint8_t v___x_3996_; 
v___x_3996_ = lean_usize_dec_lt(v_i_3994_, v_sz_3993_);
if (v___x_3996_ == 0)
{
lean_dec(v_declName_3992_);
return v_bs_3995_;
}
else
{
lean_object* v_v_3997_; lean_object* v___x_3998_; lean_object* v_bs_x27_3999_; lean_object* v___x_4000_; size_t v___x_4001_; size_t v___x_4002_; lean_object* v___x_4003_; 
v_v_3997_ = lean_array_uget(v_bs_3995_, v_i_3994_);
v___x_3998_ = lean_unsigned_to_nat(0u);
v_bs_x27_3999_ = lean_array_uset(v_bs_3995_, v_i_3994_, v___x_3998_);
lean_inc(v_declName_3992_);
v___x_4000_ = l_Lean_Meta_Simp_Simprocs_erase(v_v_3997_, v_declName_3992_);
v___x_4001_ = ((size_t)1ULL);
v___x_4002_ = lean_usize_add(v_i_3994_, v___x_4001_);
v___x_4003_ = lean_array_uset(v_bs_x27_3999_, v_i_3994_, v___x_4000_);
v_i_3994_ = v___x_4002_;
v_bs_3995_ = v___x_4003_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0___boxed(lean_object* v_declName_4005_, lean_object* v_sz_4006_, lean_object* v_i_4007_, lean_object* v_bs_4008_){
_start:
{
size_t v_sz_boxed_4009_; size_t v_i_boxed_4010_; lean_object* v_res_4011_; 
v_sz_boxed_4009_ = lean_unbox_usize(v_sz_4006_);
lean_dec(v_sz_4006_);
v_i_boxed_4010_ = lean_unbox_usize(v_i_4007_);
lean_dec(v_i_4007_);
v_res_4011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(v_declName_4005_, v_sz_boxed_4009_, v_i_boxed_4010_, v_bs_4008_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object* v_ss_4012_, lean_object* v_declName_4013_){
_start:
{
size_t v_sz_4014_; size_t v___x_4015_; lean_object* v___x_4016_; 
v_sz_4014_ = lean_array_size(v_ss_4012_);
v___x_4015_ = ((size_t)0ULL);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Simp_SimprocsArray_erase_spec__0(v_declName_4013_, v_sz_4014_, v___x_4015_, v_ss_4012_);
return v___x_4016_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(lean_object* v_declName_4017_, lean_object* v_as_4018_, size_t v_i_4019_, size_t v_stop_4020_){
_start:
{
uint8_t v___x_4021_; 
v___x_4021_ = lean_usize_dec_eq(v_i_4019_, v_stop_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; lean_object* v_erased_4023_; uint8_t v___x_4024_; 
v___x_4022_ = lean_array_uget_borrowed(v_as_4018_, v_i_4019_);
v_erased_4023_ = lean_ctor_get(v___x_4022_, 3);
lean_inc_ref(v_erased_4023_);
v___x_4024_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Simp_eraseSimprocAttr_spec__0___redArg(v_erased_4023_, v_declName_4017_);
if (v___x_4024_ == 0)
{
size_t v___x_4025_; size_t v___x_4026_; 
v___x_4025_ = ((size_t)1ULL);
v___x_4026_ = lean_usize_add(v_i_4019_, v___x_4025_);
v_i_4019_ = v___x_4026_;
goto _start;
}
else
{
return v___x_4024_;
}
}
else
{
uint8_t v___x_4028_; 
v___x_4028_ = 0;
return v___x_4028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0___boxed(lean_object* v_declName_4029_, lean_object* v_as_4030_, lean_object* v_i_4031_, lean_object* v_stop_4032_){
_start:
{
size_t v_i_boxed_4033_; size_t v_stop_boxed_4034_; uint8_t v_res_4035_; lean_object* v_r_4036_; 
v_i_boxed_4033_ = lean_unbox_usize(v_i_4031_);
lean_dec(v_i_4031_);
v_stop_boxed_4034_ = lean_unbox_usize(v_stop_4032_);
lean_dec(v_stop_4032_);
v_res_4035_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(v_declName_4029_, v_as_4030_, v_i_boxed_4033_, v_stop_boxed_4034_);
lean_dec_ref(v_as_4030_);
lean_dec(v_declName_4029_);
v_r_4036_ = lean_box(v_res_4035_);
return v_r_4036_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object* v_ss_4037_, lean_object* v_declName_4038_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v___x_4039_ = lean_unsigned_to_nat(0u);
v___x_4040_ = lean_array_get_size(v_ss_4037_);
v___x_4041_ = lean_nat_dec_lt(v___x_4039_, v___x_4040_);
if (v___x_4041_ == 0)
{
return v___x_4041_;
}
else
{
if (v___x_4041_ == 0)
{
return v___x_4041_;
}
else
{
size_t v___x_4042_; size_t v___x_4043_; uint8_t v___x_4044_; 
v___x_4042_ = ((size_t)0ULL);
v___x_4043_ = lean_usize_of_nat(v___x_4040_);
v___x_4044_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Simp_SimprocsArray_isErased_spec__0(v_declName_4038_, v_ss_4037_, v___x_4042_, v___x_4043_);
return v___x_4044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object* v_ss_4045_, lean_object* v_declName_4046_){
_start:
{
uint8_t v_res_4047_; lean_object* v_r_4048_; 
v_res_4047_ = l_Lean_Meta_Simp_SimprocsArray_isErased(v_ss_4045_, v_declName_4046_);
lean_dec(v_declName_4046_);
lean_dec_ref(v_ss_4045_);
v_r_4048_ = lean_box(v_res_4047_);
return v_r_4048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(uint8_t v_post_4049_, uint8_t v___y_4050_, lean_object* v_as_4051_, size_t v_sz_4052_, size_t v_i_4053_, lean_object* v_b_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_a_4064_; uint8_t v_cache_4068_; 
v_cache_4068_ = lean_usize_dec_lt(v_i_4053_, v_sz_4052_);
if (v_cache_4068_ == 0)
{
lean_object* v___x_4069_; 
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v_b_4054_);
return v___x_4069_;
}
else
{
lean_object* v_snd_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4213_; 
v_snd_4070_ = lean_ctor_get(v_b_4054_, 1);
v_isSharedCheck_4213_ = !lean_is_exclusive(v_b_4054_);
if (v_isSharedCheck_4213_ == 0)
{
lean_object* v_unused_4214_; 
v_unused_4214_ = lean_ctor_get(v_b_4054_, 0);
lean_dec(v_unused_4214_);
v___x_4072_ = v_b_4054_;
v_isShared_4073_ = v_isSharedCheck_4213_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_snd_4070_);
lean_dec(v_b_4054_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4213_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v_snd_4074_; lean_object* v_snd_4075_; lean_object* v_fst_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4211_; 
v_snd_4074_ = lean_ctor_get(v_snd_4070_, 1);
lean_inc(v_snd_4074_);
v_snd_4075_ = lean_ctor_get(v_snd_4074_, 1);
lean_inc(v_snd_4075_);
v_fst_4076_ = lean_ctor_get(v_snd_4070_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_snd_4070_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; 
v_unused_4212_ = lean_ctor_get(v_snd_4070_, 1);
lean_dec(v_unused_4212_);
v___x_4078_ = v_snd_4070_;
v_isShared_4079_ = v_isSharedCheck_4211_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_fst_4076_);
lean_dec(v_snd_4070_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4211_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v_fst_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4209_; 
v_fst_4080_ = lean_ctor_get(v_snd_4074_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_snd_4074_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; 
v_unused_4210_ = lean_ctor_get(v_snd_4074_, 1);
lean_dec(v_unused_4210_);
v___x_4082_ = v_snd_4074_;
v_isShared_4083_ = v_isSharedCheck_4209_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_fst_4080_);
lean_dec(v_snd_4074_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4209_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v_fst_4084_; lean_object* v_snd_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4208_; 
v_fst_4084_ = lean_ctor_get(v_snd_4075_, 0);
v_snd_4085_ = lean_ctor_get(v_snd_4075_, 1);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_snd_4075_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4087_ = v_snd_4075_;
v_isShared_4088_ = v_isSharedCheck_4208_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_snd_4085_);
lean_inc(v_fst_4084_);
lean_dec(v_snd_4075_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4208_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; lean_object* v___y_4091_; lean_object* v___y_4092_; uint8_t v___y_4093_; uint8_t v_found_4108_; lean_object* v_a_4109_; lean_object* v___y_4111_; 
v___x_4089_ = lean_box(0);
v_found_4108_ = 0;
v_a_4109_ = lean_array_uget_borrowed(v_as_4051_, v_i_4053_);
if (v___y_4050_ == 0)
{
lean_object* v_pre_4206_; 
v_pre_4206_ = lean_ctor_get(v_a_4109_, 0);
lean_inc_ref(v_pre_4206_);
v___y_4111_ = v_pre_4206_;
goto v___jp_4110_;
}
else
{
lean_object* v_post_4207_; 
v_post_4207_ = lean_ctor_get(v_a_4109_, 1);
lean_inc_ref(v_post_4207_);
v___y_4111_ = v_post_4207_;
goto v___jp_4110_;
}
v___jp_4090_:
{
lean_object* v___x_4094_; lean_object* v___x_4096_; 
v___x_4094_ = lean_box(v___y_4093_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set(v___x_4087_, 1, v___x_4094_);
lean_ctor_set(v___x_4087_, 0, v___y_4092_);
v___x_4096_ = v___x_4087_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___y_4092_);
lean_ctor_set(v_reuseFailAlloc_4107_, 1, v___x_4094_);
v___x_4096_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
lean_object* v___x_4098_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 1, v___x_4096_);
lean_ctor_set(v___x_4082_, 0, v___y_4091_);
v___x_4098_ = v___x_4082_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___y_4091_);
lean_ctor_set(v_reuseFailAlloc_4106_, 1, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4099_ = lean_box(v_cache_4068_);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 1, v___x_4098_);
lean_ctor_set(v___x_4078_, 0, v___x_4099_);
v___x_4101_ = v___x_4078_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___x_4098_);
v___x_4101_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
lean_object* v___x_4103_; 
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 1, v___x_4101_);
lean_ctor_set(v___x_4072_, 0, v___x_4089_);
v___x_4103_ = v___x_4072_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
v_a_4064_ = v___x_4103_;
goto v___jp_4063_;
}
}
}
}
}
v___jp_4110_:
{
lean_object* v_erased_4112_; lean_object* v___x_4113_; 
v_erased_4112_ = lean_ctor_get(v_a_4109_, 3);
lean_inc(v___y_4061_);
lean_inc_ref(v___y_4060_);
lean_inc(v___y_4059_);
lean_inc_ref(v___y_4058_);
lean_inc(v___y_4057_);
lean_inc_ref(v___y_4056_);
lean_inc(v___y_4055_);
lean_inc(v_fst_4080_);
lean_inc_ref(v_erased_4112_);
v___x_4113_ = l_Lean_Meta_Simp_simprocCore(v_post_4049_, v___y_4111_, v_erased_4112_, v_fst_4080_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref(v___x_4113_);
switch(lean_obj_tag(v_a_4114_))
{
case 0:
{
lean_object* v_r_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4145_; 
lean_del_object(v___x_4087_);
lean_del_object(v___x_4082_);
lean_del_object(v___x_4078_);
lean_del_object(v___x_4072_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
v_r_4115_ = lean_ctor_get(v_a_4114_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v_a_4114_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4117_ = v_a_4114_;
v_isShared_4118_ = v_isSharedCheck_4145_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_r_4115_);
lean_dec(v_a_4114_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4145_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
uint8_t v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_unbox(v_snd_4085_);
lean_inc(v_fst_4084_);
v___x_4120_ = l_Lean_Meta_Simp_mkEqTransOptProofResult(v_fst_4084_, v___x_4119_, v_r_4115_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4136_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4123_ = v___x_4120_;
v_isShared_4124_ = v_isSharedCheck_4136_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_a_4121_);
lean_dec(v___x_4120_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4136_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set(v___x_4117_, 0, v_a_4121_);
v___x_4126_ = v___x_4117_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4121_);
v___x_4126_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
v___x_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4128_, 0, v_fst_4084_);
lean_ctor_set(v___x_4128_, 1, v_snd_4085_);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v_fst_4080_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_fst_4076_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4127_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v___x_4131_);
v___x_4133_ = v___x_4123_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_del_object(v___x_4117_);
lean_dec(v_snd_4085_);
lean_dec(v_fst_4084_);
lean_dec(v_fst_4080_);
lean_dec(v_fst_4076_);
v_a_4137_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4120_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4120_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
case 1:
{
lean_object* v_e_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4176_; 
lean_del_object(v___x_4087_);
lean_del_object(v___x_4082_);
lean_del_object(v___x_4078_);
lean_del_object(v___x_4072_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
v_e_4146_ = lean_ctor_get(v_a_4114_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v_a_4114_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4148_ = v_a_4114_;
v_isShared_4149_ = v_isSharedCheck_4176_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_e_4146_);
lean_dec(v_a_4114_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4176_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
uint8_t v___x_4150_; lean_object* v___x_4151_; 
v___x_4150_ = lean_unbox(v_snd_4085_);
lean_inc(v_fst_4084_);
v___x_4151_ = l_Lean_Meta_Simp_mkEqTransOptProofResult(v_fst_4084_, v___x_4150_, v_e_4146_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4167_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4167_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4167_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v_a_4152_);
v___x_4157_ = v___x_4148_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v_fst_4084_);
lean_ctor_set(v___x_4159_, 1, v_snd_4085_);
v___x_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4160_, 0, v_fst_4080_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v_fst_4076_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4158_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4162_);
v___x_4164_ = v___x_4154_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_del_object(v___x_4148_);
lean_dec(v_snd_4085_);
lean_dec(v_fst_4084_);
lean_dec(v_fst_4080_);
lean_dec(v_fst_4076_);
v_a_4168_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4151_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4151_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
}
default: 
{
lean_object* v_e_x3f_4177_; 
v_e_x3f_4177_ = lean_ctor_get(v_a_4114_, 0);
lean_inc(v_e_x3f_4177_);
lean_dec_ref(v_a_4114_);
if (lean_obj_tag(v_e_x3f_4177_) == 0)
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_del_object(v___x_4087_);
lean_del_object(v___x_4082_);
lean_del_object(v___x_4078_);
lean_del_object(v___x_4072_);
v___x_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4178_, 0, v_fst_4084_);
lean_ctor_set(v___x_4178_, 1, v_snd_4085_);
v___x_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4179_, 0, v_fst_4080_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v_fst_4076_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4089_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v_a_4064_ = v___x_4181_;
goto v___jp_4063_;
}
else
{
lean_object* v_val_4182_; lean_object* v_expr_4183_; lean_object* v_proof_x3f_4184_; uint8_t v_cache_4185_; lean_object* v___x_4186_; 
lean_dec(v_fst_4080_);
lean_dec(v_fst_4076_);
v_val_4182_ = lean_ctor_get(v_e_x3f_4177_, 0);
lean_inc(v_val_4182_);
lean_dec_ref(v_e_x3f_4177_);
v_expr_4183_ = lean_ctor_get(v_val_4182_, 0);
lean_inc_ref(v_expr_4183_);
v_proof_x3f_4184_ = lean_ctor_get(v_val_4182_, 1);
lean_inc(v_proof_x3f_4184_);
v_cache_4185_ = lean_ctor_get_uint8(v_val_4182_, sizeof(void*)*2);
lean_dec(v_val_4182_);
lean_inc(v___y_4061_);
lean_inc_ref(v___y_4060_);
lean_inc(v___y_4059_);
lean_inc_ref(v___y_4058_);
v___x_4186_ = l_Lean_Meta_mkEqTrans_x3f(v_fst_4084_, v_proof_x3f_4184_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4186_) == 0)
{
uint8_t v___x_4187_; 
v___x_4187_ = lean_unbox(v_snd_4085_);
lean_dec(v_snd_4085_);
if (v___x_4187_ == 0)
{
lean_object* v_a_4188_; 
v_a_4188_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4188_);
lean_dec_ref(v___x_4186_);
v___y_4091_ = v_expr_4183_;
v___y_4092_ = v_a_4188_;
v___y_4093_ = v_found_4108_;
goto v___jp_4090_;
}
else
{
lean_object* v_a_4189_; 
v_a_4189_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_a_4189_);
lean_dec_ref(v___x_4186_);
v___y_4091_ = v_expr_4183_;
v___y_4092_ = v_a_4189_;
v___y_4093_ = v_cache_4185_;
goto v___jp_4090_;
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec_ref(v_expr_4183_);
lean_del_object(v___x_4087_);
lean_dec(v_snd_4085_);
lean_del_object(v___x_4082_);
lean_del_object(v___x_4078_);
lean_del_object(v___x_4072_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
v_a_4190_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4186_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4186_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_del_object(v___x_4087_);
lean_dec(v_snd_4085_);
lean_dec(v_fst_4084_);
lean_del_object(v___x_4082_);
lean_dec(v_fst_4080_);
lean_del_object(v___x_4078_);
lean_dec(v_fst_4076_);
lean_del_object(v___x_4072_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
v_a_4198_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4113_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4113_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
}
}
}
}
v___jp_4063_:
{
size_t v___x_4065_; size_t v___x_4066_; 
v___x_4065_ = ((size_t)1ULL);
v___x_4066_ = lean_usize_add(v_i_4053_, v___x_4065_);
v_i_4053_ = v___x_4066_;
v_b_4054_ = v_a_4064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0___boxed(lean_object* v_post_4215_, lean_object* v___y_4216_, lean_object* v_as_4217_, lean_object* v_sz_4218_, lean_object* v_i_4219_, lean_object* v_b_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
uint8_t v_post_boxed_4229_; uint8_t v___y_5820__boxed_4230_; size_t v_sz_boxed_4231_; size_t v_i_boxed_4232_; lean_object* v_res_4233_; 
v_post_boxed_4229_ = lean_unbox(v_post_4215_);
v___y_5820__boxed_4230_ = lean_unbox(v___y_4216_);
v_sz_boxed_4231_ = lean_unbox_usize(v_sz_4218_);
lean_dec(v_sz_4218_);
v_i_boxed_4232_ = lean_unbox_usize(v_i_4219_);
lean_dec(v_i_4219_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(v_post_boxed_4229_, v___y_5820__boxed_4230_, v_as_4217_, v_sz_boxed_4231_, v_i_boxed_4232_, v_b_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec_ref(v_as_4217_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t v_post_4238_, lean_object* v_ss_4239_, lean_object* v_e_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_){
_start:
{
uint8_t v_found_4249_; lean_object* v_proof_x3f_4250_; uint8_t v_cache_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; size_t v_sz_4257_; size_t v___x_4258_; lean_object* v___x_4259_; 
v_found_4249_ = 0;
v_proof_x3f_4250_ = lean_box(0);
v_cache_4251_ = 1;
v___x_4252_ = ((lean_object*)(l_Lean_Meta_Simp_simprocArrayCore___closed__0));
v___x_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4253_, 0, v_e_4240_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = lean_box(v_found_4249_);
v___x_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4254_);
lean_ctor_set(v___x_4255_, 1, v___x_4253_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_proof_x3f_4250_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v_sz_4257_ = lean_array_size(v_ss_4239_);
v___x_4258_ = ((size_t)0ULL);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_simprocArrayCore_spec__0(v_post_4238_, v_post_4238_, v_ss_4239_, v_sz_4257_, v___x_4258_, v___x_4256_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4286_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4286_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4286_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v_snd_4264_; lean_object* v_snd_4265_; lean_object* v_snd_4266_; lean_object* v_fst_4267_; 
v_snd_4264_ = lean_ctor_get(v_a_4260_, 1);
lean_inc(v_snd_4264_);
v_snd_4265_ = lean_ctor_get(v_snd_4264_, 1);
lean_inc(v_snd_4265_);
v_snd_4266_ = lean_ctor_get(v_snd_4265_, 1);
lean_inc(v_snd_4266_);
v_fst_4267_ = lean_ctor_get(v_a_4260_, 0);
lean_inc(v_fst_4267_);
lean_dec(v_a_4260_);
if (lean_obj_tag(v_fst_4267_) == 0)
{
lean_object* v_fst_4268_; uint8_t v___x_4269_; 
v_fst_4268_ = lean_ctor_get(v_snd_4264_, 0);
lean_inc(v_fst_4268_);
lean_dec(v_snd_4264_);
v___x_4269_ = lean_unbox(v_fst_4268_);
lean_dec(v_fst_4268_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; lean_object* v___x_4272_; 
lean_dec(v_snd_4266_);
lean_dec(v_snd_4265_);
v___x_4270_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__5));
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___x_4270_);
v___x_4272_ = v___x_4262_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
else
{
lean_object* v_fst_4274_; lean_object* v_fst_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4280_; 
v_fst_4274_ = lean_ctor_get(v_snd_4265_, 0);
lean_inc(v_fst_4274_);
lean_dec(v_snd_4265_);
v_fst_4275_ = lean_ctor_get(v_snd_4266_, 0);
lean_inc(v_fst_4275_);
lean_dec(v_snd_4266_);
v___x_4276_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4276_, 0, v_fst_4274_);
lean_ctor_set(v___x_4276_, 1, v_fst_4275_);
lean_ctor_set_uint8(v___x_4276_, sizeof(void*)*2, v_cache_4251_);
v___x_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
v___x_4278_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v___x_4278_);
v___x_4280_ = v___x_4262_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v___x_4278_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
else
{
lean_object* v_val_4282_; lean_object* v___x_4284_; 
lean_dec(v_snd_4266_);
lean_dec(v_snd_4265_);
lean_dec(v_snd_4264_);
v_val_4282_ = lean_ctor_get(v_fst_4267_, 0);
lean_inc(v_val_4282_);
lean_dec_ref(v_fst_4267_);
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v_val_4282_);
v___x_4284_ = v___x_4262_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_val_4282_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
v_a_4287_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4259_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4259_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object* v_post_4295_, lean_object* v_ss_4296_, lean_object* v_e_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
uint8_t v_post_boxed_4306_; lean_object* v_res_4307_; 
v_post_boxed_4306_ = lean_unbox(v_post_4295_);
v_res_4307_ = l_Lean_Meta_Simp_simprocArrayCore(v_post_boxed_4306_, v_ss_4296_, v_e_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec_ref(v_ss_4296_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(uint8_t v_post_4308_, lean_object* v_as_4309_, size_t v_sz_4310_, size_t v_i_4311_, lean_object* v_b_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_a_4322_; uint8_t v___x_4326_; 
v___x_4326_ = lean_usize_dec_lt(v_i_4311_, v_sz_4310_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; 
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v_b_4312_);
return v___x_4327_;
}
else
{
lean_object* v_snd_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4384_; 
v_snd_4328_ = lean_ctor_get(v_b_4312_, 1);
v_isSharedCheck_4384_ = !lean_is_exclusive(v_b_4312_);
if (v_isSharedCheck_4384_ == 0)
{
lean_object* v_unused_4385_; 
v_unused_4385_ = lean_ctor_get(v_b_4312_, 0);
lean_dec(v_unused_4385_);
v___x_4330_ = v_b_4312_;
v_isShared_4331_ = v_isSharedCheck_4384_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_snd_4328_);
lean_dec(v_b_4312_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4384_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v_fst_4332_; lean_object* v_snd_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4383_; 
v_fst_4332_ = lean_ctor_get(v_snd_4328_, 0);
v_snd_4333_ = lean_ctor_get(v_snd_4328_, 1);
v_isSharedCheck_4383_ = !lean_is_exclusive(v_snd_4328_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4335_ = v_snd_4328_;
v_isShared_4336_ = v_isSharedCheck_4383_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_snd_4333_);
lean_inc(v_fst_4332_);
lean_dec(v_snd_4328_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4383_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4337_; lean_object* v_a_4338_; lean_object* v___y_4340_; 
v___x_4337_ = lean_box(0);
v_a_4338_ = lean_array_uget_borrowed(v_as_4309_, v_i_4311_);
if (v_post_4308_ == 0)
{
lean_object* v_pre_4381_; 
v_pre_4381_ = lean_ctor_get(v_a_4338_, 0);
lean_inc_ref(v_pre_4381_);
v___y_4340_ = v_pre_4381_;
goto v___jp_4339_;
}
else
{
lean_object* v_post_4382_; 
v_post_4382_ = lean_ctor_get(v_a_4338_, 1);
lean_inc_ref(v_post_4382_);
v___y_4340_ = v_post_4382_;
goto v___jp_4339_;
}
v___jp_4339_:
{
lean_object* v_erased_4341_; lean_object* v___x_4342_; 
v_erased_4341_ = lean_ctor_get(v_a_4338_, 3);
lean_inc(v___y_4319_);
lean_inc_ref(v___y_4318_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
lean_inc(v___y_4313_);
lean_inc(v_snd_4333_);
lean_inc_ref(v_erased_4341_);
v___x_4342_ = l_Lean_Meta_Simp_dsimprocCore(v_post_4308_, v___y_4340_, v_erased_4341_, v_snd_4333_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4372_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4372_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4372_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
if (lean_obj_tag(v_a_4343_) == 2)
{
lean_object* v_e_x3f_4347_; 
lean_del_object(v___x_4345_);
v_e_x3f_4347_ = lean_ctor_get(v_a_4343_, 0);
lean_inc(v_e_x3f_4347_);
lean_dec_ref(v_a_4343_);
if (lean_obj_tag(v_e_x3f_4347_) == 0)
{
lean_object* v___x_4349_; 
if (v_isShared_4336_ == 0)
{
v___x_4349_ = v___x_4335_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_fst_4332_);
lean_ctor_set(v_reuseFailAlloc_4353_, 1, v_snd_4333_);
v___x_4349_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4351_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 1, v___x_4349_);
lean_ctor_set(v___x_4330_, 0, v___x_4337_);
v___x_4351_ = v___x_4330_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v___x_4349_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
v_a_4322_ = v___x_4351_;
goto v___jp_4321_;
}
}
}
else
{
lean_object* v_val_4354_; lean_object* v___x_4355_; lean_object* v___x_4357_; 
lean_dec(v_snd_4333_);
lean_dec(v_fst_4332_);
v_val_4354_ = lean_ctor_get(v_e_x3f_4347_, 0);
lean_inc(v_val_4354_);
lean_dec_ref(v_e_x3f_4347_);
v___x_4355_ = lean_box(v___x_4326_);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 1, v_val_4354_);
lean_ctor_set(v___x_4335_, 0, v___x_4355_);
v___x_4357_ = v___x_4335_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4361_, 1, v_val_4354_);
v___x_4357_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
lean_object* v___x_4359_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 1, v___x_4357_);
lean_ctor_set(v___x_4330_, 0, v___x_4337_);
v___x_4359_ = v___x_4330_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4337_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
v_a_4322_ = v___x_4359_;
goto v___jp_4321_;
}
}
}
}
else
{
lean_object* v___x_4362_; lean_object* v___x_4364_; 
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
v___x_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_a_4343_);
if (v_isShared_4336_ == 0)
{
v___x_4364_ = v___x_4335_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_fst_4332_);
lean_ctor_set(v_reuseFailAlloc_4371_, 1, v_snd_4333_);
v___x_4364_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
lean_object* v___x_4366_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 1, v___x_4364_);
lean_ctor_set(v___x_4330_, 0, v___x_4362_);
v___x_4366_ = v___x_4330_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4362_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4368_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4366_);
v___x_4368_ = v___x_4345_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4366_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_del_object(v___x_4335_);
lean_dec(v_snd_4333_);
lean_dec(v_fst_4332_);
lean_del_object(v___x_4330_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
v_a_4373_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4342_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4342_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
}
}
}
v___jp_4321_:
{
size_t v___x_4323_; size_t v___x_4324_; 
v___x_4323_ = ((size_t)1ULL);
v___x_4324_ = lean_usize_add(v_i_4311_, v___x_4323_);
v_i_4311_ = v___x_4324_;
v_b_4312_ = v_a_4322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0___boxed(lean_object* v_post_4386_, lean_object* v_as_4387_, lean_object* v_sz_4388_, lean_object* v_i_4389_, lean_object* v_b_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
uint8_t v_post_boxed_4399_; size_t v_sz_boxed_4400_; size_t v_i_boxed_4401_; lean_object* v_res_4402_; 
v_post_boxed_4399_ = lean_unbox(v_post_4386_);
v_sz_boxed_4400_ = lean_unbox_usize(v_sz_4388_);
lean_dec(v_sz_4388_);
v_i_boxed_4401_ = lean_unbox_usize(v_i_4389_);
lean_dec(v_i_4389_);
v_res_4402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(v_post_boxed_4399_, v_as_4387_, v_sz_boxed_4400_, v_i_boxed_4401_, v_b_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec_ref(v_as_4387_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t v_post_4403_, lean_object* v_ss_4404_, lean_object* v_e_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_){
_start:
{
uint8_t v_found_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; size_t v_sz_4419_; size_t v___x_4420_; lean_object* v___x_4421_; 
v_found_4414_ = 0;
v___x_4415_ = lean_box(0);
v___x_4416_ = lean_box(v_found_4414_);
v___x_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
lean_ctor_set(v___x_4417_, 1, v_e_4405_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4415_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v_sz_4419_ = lean_array_size(v_ss_4404_);
v___x_4420_ = ((size_t)0ULL);
v___x_4421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Simp_dsimprocArrayCore_spec__0(v_post_4403_, v_ss_4404_, v_sz_4419_, v___x_4420_, v___x_4418_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4444_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4444_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4444_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v_fst_4426_; 
v_fst_4426_ = lean_ctor_get(v_a_4422_, 0);
if (lean_obj_tag(v_fst_4426_) == 0)
{
lean_object* v_snd_4427_; lean_object* v_fst_4428_; uint8_t v___x_4429_; 
v_snd_4427_ = lean_ctor_get(v_a_4422_, 1);
lean_inc(v_snd_4427_);
lean_dec(v_a_4422_);
v_fst_4428_ = lean_ctor_get(v_snd_4427_, 0);
v___x_4429_ = lean_unbox(v_fst_4428_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4432_; 
lean_dec(v_snd_4427_);
v___x_4430_ = ((lean_object*)(l_Lean_Meta_Simp_dsimprocCore___closed__0));
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4430_);
v___x_4432_ = v___x_4424_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
else
{
lean_object* v_snd_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4438_; 
v_snd_4434_ = lean_ctor_get(v_snd_4427_, 1);
lean_inc(v_snd_4434_);
lean_dec(v_snd_4427_);
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v_snd_4434_);
v___x_4436_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4435_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4436_);
v___x_4438_ = v___x_4424_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
else
{
lean_object* v_val_4440_; lean_object* v___x_4442_; 
lean_inc_ref(v_fst_4426_);
lean_dec(v_a_4422_);
v_val_4440_ = lean_ctor_get(v_fst_4426_, 0);
lean_inc(v_val_4440_);
lean_dec_ref(v_fst_4426_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v_val_4440_);
v___x_4442_ = v___x_4424_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_val_4440_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
v_a_4445_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4421_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4421_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object* v_post_4453_, lean_object* v_ss_4454_, lean_object* v_e_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_){
_start:
{
uint8_t v_post_boxed_4464_; lean_object* v_res_4465_; 
v_post_boxed_4464_ = lean_unbox(v_post_4453_);
v_res_4465_ = l_Lean_Meta_Simp_dsimprocArrayCore(v_post_boxed_4464_, v_ss_4454_, v_e_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
lean_dec_ref(v_ss_4454_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(lean_object* v_name_4466_, lean_object* v_decl_4467_, lean_object* v_ref_4468_){
_start:
{
lean_object* v_defValue_4470_; lean_object* v_descr_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4498_; 
v_defValue_4470_ = lean_ctor_get(v_decl_4467_, 0);
v_descr_4471_ = lean_ctor_get(v_decl_4467_, 1);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_decl_4467_);
if (v_isSharedCheck_4498_ == 0)
{
v___x_4473_ = v_decl_4467_;
v_isShared_4474_ = v_isSharedCheck_4498_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_descr_4471_);
lean_inc(v_defValue_4470_);
lean_dec(v_decl_4467_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4498_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4475_ = lean_alloc_ctor(1, 0, 1);
v___x_4476_ = lean_unbox(v_defValue_4470_);
lean_ctor_set_uint8(v___x_4475_, 0, v___x_4476_);
lean_inc(v_name_4466_);
v___x_4477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4477_, 0, v_name_4466_);
lean_ctor_set(v___x_4477_, 1, v_ref_4468_);
lean_ctor_set(v___x_4477_, 2, v___x_4475_);
lean_ctor_set(v___x_4477_, 3, v_descr_4471_);
lean_inc(v_name_4466_);
v___x_4478_ = lean_register_option(v_name_4466_, v___x_4477_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4488_; 
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; 
v_unused_4489_ = lean_ctor_get(v___x_4478_, 0);
lean_dec(v_unused_4489_);
v___x_4480_ = v___x_4478_;
v_isShared_4481_ = v_isSharedCheck_4488_;
goto v_resetjp_4479_;
}
else
{
lean_dec(v___x_4478_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4488_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4474_ == 0)
{
lean_ctor_set(v___x_4473_, 1, v_defValue_4470_);
lean_ctor_set(v___x_4473_, 0, v_name_4466_);
v___x_4483_ = v___x_4473_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_name_4466_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v_defValue_4470_);
v___x_4483_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4485_; 
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 0, v___x_4483_);
v___x_4485_ = v___x_4480_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
else
{
lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4497_; 
lean_del_object(v___x_4473_);
lean_dec(v_defValue_4470_);
lean_dec(v_name_4466_);
v_a_4490_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4492_ = v___x_4478_;
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4478_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4497_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4495_; 
if (v_isShared_4493_ == 0)
{
v___x_4495_ = v___x_4492_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v_a_4490_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_4499_, lean_object* v_decl_4500_, lean_object* v_ref_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(v_name_4499_, v_decl_4500_, v_ref_4501_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4518_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_));
v___x_4519_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_));
v___x_4520_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__4_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_));
v___x_4521_ = l_Lean_Option_register___at___00Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4__spec__0(v___x_4518_, v___x_4519_, v___x_4520_);
return v___x_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4____boxed(lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1784667116____hygCtx___hyg_4_();
return v_res_4523_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(lean_object* v_opts_4524_, lean_object* v_opt_4525_){
_start:
{
lean_object* v_name_4526_; lean_object* v_defValue_4527_; lean_object* v_map_4528_; lean_object* v___x_4529_; 
v_name_4526_ = lean_ctor_get(v_opt_4525_, 0);
v_defValue_4527_ = lean_ctor_get(v_opt_4525_, 1);
v_map_4528_ = lean_ctor_get(v_opts_4524_, 0);
v___x_4529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4528_, v_name_4526_);
if (lean_obj_tag(v___x_4529_) == 0)
{
uint8_t v___x_4530_; 
v___x_4530_ = lean_unbox(v_defValue_4527_);
return v___x_4530_;
}
else
{
lean_object* v_val_4531_; 
v_val_4531_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_val_4531_);
lean_dec_ref(v___x_4529_);
if (lean_obj_tag(v_val_4531_) == 1)
{
uint8_t v_v_4532_; 
v_v_4532_ = lean_ctor_get_uint8(v_val_4531_, 0);
lean_dec_ref(v_val_4531_);
return v_v_4532_;
}
else
{
uint8_t v___x_4533_; 
lean_dec(v_val_4531_);
v___x_4533_ = lean_unbox(v_defValue_4527_);
return v___x_4533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0___boxed(lean_object* v_opts_4534_, lean_object* v_opt_4535_){
_start:
{
uint8_t v_res_4536_; lean_object* v_r_4537_; 
v_res_4536_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_opts_4534_, v_opt_4535_);
lean_dec_ref(v_opt_4535_);
lean_dec_ref(v_opts_4534_);
v_r_4537_ = lean_box(v_res_4536_);
return v_r_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object* v_s_4538_, lean_object* v_e_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_options_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; 
v_options_4548_ = lean_ctor_get(v_a_4545_, 2);
v___x_4549_ = l_Lean_Meta_Simp_simprocs;
v___x_4550_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4548_, v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec_ref(v_e_4539_);
v___x_4551_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__0));
v___x_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
return v___x_4552_;
}
else
{
uint8_t v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = 0;
v___x_4554_ = l_Lean_Meta_Simp_simprocArrayCore(v___x_4553_, v_s_4538_, v_e_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object* v_s_4555_, lean_object* v_e_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_){
_start:
{
lean_object* v_res_4565_; 
v_res_4565_ = l_Lean_Meta_Simp_userPreSimprocs(v_s_4555_, v_e_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
lean_dec_ref(v_s_4555_);
return v_res_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object* v_s_4566_, lean_object* v_e_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v_options_4576_; lean_object* v___x_4577_; uint8_t v___x_4578_; 
v_options_4576_ = lean_ctor_get(v_a_4573_, 2);
v___x_4577_ = l_Lean_Meta_Simp_simprocs;
v___x_4578_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4576_, v___x_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_e_4567_);
v___x_4579_ = ((lean_object*)(l_Lean_Meta_Simp_simprocCore___closed__0));
v___x_4580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4579_);
return v___x_4580_;
}
else
{
lean_object* v___x_4581_; 
v___x_4581_ = l_Lean_Meta_Simp_simprocArrayCore(v___x_4578_, v_s_4566_, v_e_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object* v_s_4582_, lean_object* v_e_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Lean_Meta_Simp_userPostSimprocs(v_s_4582_, v_e_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
lean_dec_ref(v_s_4582_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object* v_s_4593_, lean_object* v_e_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_options_4603_; lean_object* v___x_4604_; uint8_t v___x_4605_; 
v_options_4603_ = lean_ctor_get(v_a_4600_, 2);
v___x_4604_ = l_Lean_Meta_Simp_simprocs;
v___x_4605_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4603_, v___x_4604_);
if (v___x_4605_ == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_e_4594_);
v___x_4606_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
v___x_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
return v___x_4607_;
}
else
{
uint8_t v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = 0;
v___x_4609_ = l_Lean_Meta_Simp_dsimprocArrayCore(v___x_4608_, v_s_4593_, v_e_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
return v___x_4609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object* v_s_4610_, lean_object* v_e_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_){
_start:
{
lean_object* v_res_4620_; 
v_res_4620_ = l_Lean_Meta_Simp_userPreDSimprocs(v_s_4610_, v_e_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
lean_dec_ref(v_s_4610_);
return v_res_4620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object* v_s_4621_, lean_object* v_e_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_){
_start:
{
lean_object* v_options_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; 
v_options_4631_ = lean_ctor_get(v_a_4628_, 2);
v___x_4632_ = l_Lean_Meta_Simp_simprocs;
v___x_4633_ = l_Lean_Option_get___at___00Lean_Meta_Simp_userPreSimprocs_spec__0(v_options_4631_, v___x_4632_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_e_4622_);
v___x_4634_ = ((lean_object*)(l_Lean_Meta_Simp_SimprocEntry_tryD___closed__0));
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
return v___x_4635_;
}
else
{
lean_object* v___x_4636_; 
v___x_4636_ = l_Lean_Meta_Simp_dsimprocArrayCore(v___x_4633_, v_s_4621_, v_e_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
return v___x_4636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object* v_s_4637_, lean_object* v_e_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Meta_Simp_userPostDSimprocs(v_s_4637_, v_e_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec_ref(v_s_4637_);
return v_res_4647_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10(void){
_start:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4672_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__8));
v___x_4673_ = l_Lean_mkAtom(v___x_4672_);
return v___x_4673_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11(void){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4674_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__10);
v___x_4675_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4676_ = lean_array_push(v___x_4675_, v___x_4674_);
return v___x_4676_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16(void){
_start:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; 
v___x_4685_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__15));
v___x_4686_ = l_Lean_mkAtom(v___x_4685_);
return v___x_4686_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17(void){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4687_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__16);
v___x_4688_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4689_ = lean_array_push(v___x_4688_, v___x_4687_);
return v___x_4689_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4690_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__17);
v___x_4691_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__14));
v___x_4692_ = lean_box(2);
v___x_4693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4692_);
lean_ctor_set(v___x_4693_, 1, v___x_4691_);
lean_ctor_set(v___x_4693_, 2, v___x_4690_);
return v___x_4693_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4694_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__18);
v___x_4695_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__11);
v___x_4696_ = lean_array_push(v___x_4695_, v___x_4694_);
return v___x_4696_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4697_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__19);
v___x_4698_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__9));
v___x_4699_ = lean_box(2);
v___x_4700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4699_);
lean_ctor_set(v___x_4700_, 1, v___x_4698_);
lean_ctor_set(v___x_4700_, 2, v___x_4697_);
return v___x_4700_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; 
v___x_4701_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__20);
v___x_4702_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4703_ = lean_array_push(v___x_4702_, v___x_4701_);
return v___x_4703_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4704_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__21);
v___x_4705_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__7));
v___x_4706_ = lean_box(2);
v___x_4707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
lean_ctor_set(v___x_4707_, 1, v___x_4705_);
lean_ctor_set(v___x_4707_, 2, v___x_4704_);
return v___x_4707_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__22);
v___x_4709_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4710_ = lean_array_push(v___x_4709_, v___x_4708_);
return v___x_4710_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4711_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__23);
v___x_4712_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__5));
v___x_4713_ = lean_box(2);
v___x_4714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4713_);
lean_ctor_set(v___x_4714_, 1, v___x_4712_);
lean_ctor_set(v___x_4714_, 2, v___x_4711_);
return v___x_4714_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__24);
v___x_4716_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__3));
v___x_4717_ = lean_array_push(v___x_4716_, v___x_4715_);
return v___x_4717_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4718_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__25);
v___x_4719_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__2));
v___x_4720_ = lean_box(2);
v___x_4721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
lean_ctor_set(v___x_4721_, 1, v___x_4719_);
lean_ctor_set(v___x_4721_, 2, v___x_4718_);
return v___x_4721_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1(void){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0(uint8_t v_x_4723_, lean_object* v___y_4724_){
_start:
{
lean_object* v___x_4725_; 
v___x_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4725_, 0, v___y_4724_);
return v___x_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0___boxed(lean_object* v_x_4726_, lean_object* v___y_4727_){
_start:
{
uint8_t v_x_256__boxed_4728_; lean_object* v_res_4729_; 
v_x_256__boxed_4728_ = lean_unbox(v_x_4726_);
v_res_4729_ = l_Lean_Meta_Simp_mkSimprocExt___lam__0(v_x_256__boxed_4728_, v___y_4727_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1(lean_object* v_s_4730_, lean_object* v_e_4731_){
_start:
{
lean_object* v_toSimprocOLeanEntry_4732_; lean_object* v_proc_4733_; lean_object* v_declName_4734_; uint8_t v_post_4735_; lean_object* v_keys_4736_; lean_object* v___x_4737_; 
v_toSimprocOLeanEntry_4732_ = lean_ctor_get(v_e_4731_, 0);
lean_inc_ref(v_toSimprocOLeanEntry_4732_);
v_proc_4733_ = lean_ctor_get(v_e_4731_, 1);
lean_inc_ref(v_proc_4733_);
lean_dec_ref(v_e_4731_);
v_declName_4734_ = lean_ctor_get(v_toSimprocOLeanEntry_4732_, 0);
lean_inc(v_declName_4734_);
v_post_4735_ = lean_ctor_get_uint8(v_toSimprocOLeanEntry_4732_, sizeof(void*)*2);
v_keys_4736_ = lean_ctor_get(v_toSimprocOLeanEntry_4732_, 1);
lean_inc_ref(v_keys_4736_);
lean_dec_ref(v_toSimprocOLeanEntry_4732_);
v___x_4737_ = l_Lean_Meta_Simp_Simprocs_addCore(v_s_4730_, v_keys_4736_, v_declName_4734_, v_post_4735_, v_proc_4733_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2(lean_object* v_e_4738_){
_start:
{
lean_object* v_toSimprocOLeanEntry_4739_; 
v_toSimprocOLeanEntry_4739_ = lean_ctor_get(v_e_4738_, 0);
lean_inc_ref(v_toSimprocOLeanEntry_4739_);
return v_toSimprocOLeanEntry_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed(lean_object* v_e_4740_){
_start:
{
lean_object* v_res_4741_; 
v_res_4741_ = l_Lean_Meta_Simp_mkSimprocExt___lam__2(v_e_4740_);
lean_dec_ref(v_e_4740_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3(lean_object* v_x_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; 
v___x_4746_ = l_Lean_Meta_Simp_toSimprocEntry(v___y_4743_, v___y_4744_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed(lean_object* v_x_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_){
_start:
{
lean_object* v_res_4751_; 
v_res_4751_ = l_Lean_Meta_Simp_mkSimprocExt___lam__3(v_x_4747_, v___y_4748_, v___y_4749_);
lean_dec_ref(v_x_4747_);
return v_res_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4(lean_object* v_ref_x3f_4752_){
_start:
{
if (lean_obj_tag(v_ref_x3f_4752_) == 1)
{
lean_object* v_val_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4762_; 
v_val_4754_ = lean_ctor_get(v_ref_x3f_4752_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_ref_x3f_4752_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4756_ = v_ref_x3f_4752_;
v_isShared_4757_ = v_isSharedCheck_4762_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_val_4754_);
lean_dec(v_ref_x3f_4752_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4762_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4758_ = lean_st_ref_get(v_val_4754_);
lean_dec(v_val_4754_);
if (v_isShared_4757_ == 0)
{
lean_ctor_set_tag(v___x_4756_, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4758_);
v___x_4760_ = v___x_4756_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
else
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
lean_dec(v_ref_x3f_4752_);
v___x_4763_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_4225812397____hygCtx___hyg_2_);
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
return v___x_4764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed(lean_object* v_ref_x3f_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Meta_Simp_mkSimprocExt___lam__4(v_ref_x3f_4765_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__5(lean_object* v___y_4768_){
_start:
{
lean_inc_ref(v___y_4768_);
return v___y_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__5___boxed(lean_object* v___y_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Lean_Meta_Simp_mkSimprocExt___lam__5(v___y_4769_);
lean_dec_ref(v___y_4769_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object* v_name_4776_, lean_object* v_ref_x3f_4777_){
_start:
{
lean_object* v___f_4779_; lean_object* v___f_4780_; lean_object* v___f_4781_; lean_object* v___f_4782_; lean_object* v___y_4783_; lean_object* v___f_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___f_4779_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__0));
v___f_4780_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__1));
v___f_4781_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__2));
v___f_4782_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__3));
v___y_4783_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed), 2, 1);
lean_closure_set(v___y_4783_, 0, v_ref_x3f_4777_);
v___f_4784_ = ((lean_object*)(l_Lean_Meta_Simp_mkSimprocExt___closed__4));
v___x_4785_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4785_, 0, v_name_4776_);
lean_ctor_set(v___x_4785_, 1, v___y_4783_);
lean_ctor_set(v___x_4785_, 2, v___f_4782_);
lean_ctor_set(v___x_4785_, 3, v___f_4781_);
lean_ctor_set(v___x_4785_, 4, v___f_4780_);
lean_ctor_set(v___x_4785_, 5, v___f_4784_);
lean_ctor_set(v___x_4785_, 6, v___f_4779_);
v___x_4786_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___boxed(lean_object* v_name_4787_, lean_object* v_ref_x3f_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v_res_4790_; 
v_res_4790_ = l_Lean_Meta_Simp_mkSimprocExt(v_name_4787_, v_ref_x3f_4788_);
return v_res_4790_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__0(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1);
v___x_4792_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
lean_ctor_set(v___x_4792_, 2, v___x_4791_);
lean_ctor_set(v___x_4792_, 3, v___x_4791_);
lean_ctor_set(v___x_4792_, 4, v___x_4791_);
lean_ctor_set(v___x_4792_, 5, v___x_4791_);
return v___x_4792_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__1(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4793_ = lean_unsigned_to_nat(32u);
v___x_4794_ = lean_mk_empty_array_with_capacity(v___x_4793_);
v___x_4795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__2(void){
_start:
{
size_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4796_ = ((size_t)5ULL);
v___x_4797_ = lean_unsigned_to_nat(0u);
v___x_4798_ = lean_unsigned_to_nat(32u);
v___x_4799_ = lean_mk_empty_array_with_capacity(v___x_4798_);
v___x_4800_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__1, &l_Lean_Meta_Simp_addSimprocAttr___closed__1_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__1);
v___x_4801_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
lean_ctor_set(v___x_4801_, 1, v___x_4799_);
lean_ctor_set(v___x_4801_, 2, v___x_4797_);
lean_ctor_set(v___x_4801_, 3, v___x_4797_);
lean_ctor_set_usize(v___x_4801_, 4, v___x_4796_);
return v___x_4801_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__3(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; 
v___x_4802_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__1);
v___x_4803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
lean_ctor_set(v___x_4803_, 2, v___x_4802_);
lean_ctor_set(v___x_4803_, 3, v___x_4802_);
lean_ctor_set(v___x_4803_, 4, v___x_4802_);
return v___x_4803_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_addSimprocAttr___closed__4(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4804_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__3, &l_Lean_Meta_Simp_addSimprocAttr___closed__3_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__3);
v___x_4805_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__2, &l_Lean_Meta_Simp_addSimprocAttr___closed__2_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__2);
v___x_4806_ = lean_box(1);
v___x_4807_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__0, &l_Lean_Meta_Simp_addSimprocAttr___closed__0_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__0);
v___x_4808_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2);
v___x_4809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
lean_ctor_set(v___x_4809_, 1, v___x_4807_);
lean_ctor_set(v___x_4809_, 2, v___x_4806_);
lean_ctor_set(v___x_4809_, 3, v___x_4805_);
lean_ctor_set(v___x_4809_, 4, v___x_4804_);
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object* v_attrName_4816_, lean_object* v_ext_4817_, lean_object* v_declName_4818_, lean_object* v_stx_4819_, uint8_t v_attrKind_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v___x_4824_; 
lean_inc(v_a_4822_);
lean_inc_ref(v_a_4821_);
lean_inc(v_declName_4818_);
v___x_4824_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_4816_, v_declName_4818_, v_attrKind_4820_, v_a_4821_, v_a_4822_);
if (lean_obj_tag(v___x_4824_) == 0)
{
uint8_t v___y_4826_; lean_object* v___x_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
lean_dec_ref(v___x_4824_);
v___x_4840_ = lean_unsigned_to_nat(1u);
v___x_4841_ = l_Lean_Syntax_getArg(v_stx_4819_, v___x_4840_);
v___x_4842_ = l_Lean_Syntax_isNone(v___x_4841_);
if (v___x_4842_ == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; uint8_t v___x_4847_; 
v___x_4843_ = lean_unsigned_to_nat(0u);
v___x_4844_ = l_Lean_Syntax_getArg(v___x_4841_, v___x_4843_);
lean_dec(v___x_4841_);
v___x_4845_ = l_Lean_Syntax_getKind(v___x_4844_);
v___x_4846_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocAttr___closed__6));
v___x_4847_ = lean_name_eq(v___x_4845_, v___x_4846_);
lean_dec(v___x_4845_);
v___y_4826_ = v___x_4847_;
goto v___jp_4825_;
}
else
{
lean_dec(v___x_4841_);
v___y_4826_ = v___x_4842_;
goto v___jp_4825_;
}
v___jp_4825_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = lean_obj_once(&l_Lean_Meta_Simp_addSimprocAttr___closed__4, &l_Lean_Meta_Simp_addSimprocAttr___closed__4_once, _init_l_Lean_Meta_Simp_addSimprocAttr___closed__4);
v___x_4828_ = lean_st_mk_ref(v___x_4827_);
v___x_4829_ = l_Lean_Meta_Simp_addSimprocAttrCore(v_ext_4817_, v_declName_4818_, v_attrKind_4820_, v___y_4826_, v_a_4821_, v_a_4822_);
lean_dec(v_a_4822_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4838_; 
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v___x_4829_, 0);
lean_dec(v_unused_4839_);
v___x_4831_ = v___x_4829_;
v_isShared_4832_ = v_isSharedCheck_4838_;
goto v_resetjp_4830_;
}
else
{
lean_dec(v___x_4829_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4838_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4833_ = lean_st_ref_get(v___x_4828_);
lean_dec(v___x_4828_);
lean_dec(v___x_4833_);
v___x_4834_ = lean_box(0);
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 0, v___x_4834_);
v___x_4836_ = v___x_4831_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
else
{
lean_dec(v___x_4828_);
return v___x_4829_;
}
}
}
else
{
lean_dec(v_a_4822_);
lean_dec_ref(v_a_4821_);
lean_dec(v_declName_4818_);
lean_dec_ref(v_ext_4817_);
return v___x_4824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object* v_attrName_4848_, lean_object* v_ext_4849_, lean_object* v_declName_4850_, lean_object* v_stx_4851_, lean_object* v_attrKind_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
uint8_t v_attrKind_boxed_4856_; lean_object* v_res_4857_; 
v_attrKind_boxed_4856_ = lean_unbox(v_attrKind_4852_);
v_res_4857_ = l_Lean_Meta_Simp_addSimprocAttr(v_attrName_4848_, v_ext_4849_, v_declName_4850_, v_stx_4851_, v_attrKind_boxed_4856_, v_a_4853_, v_a_4854_);
lean_dec(v_stx_4851_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object* v_attrName_4858_, lean_object* v_attrDescr_4859_, lean_object* v_ext_4860_, lean_object* v_name_4861_){
_start:
{
uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4863_ = 1;
lean_inc(v_attrName_4858_);
v___x_4864_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_4864_, 0, v_name_4861_);
lean_ctor_set(v___x_4864_, 1, v_attrName_4858_);
lean_ctor_set(v___x_4864_, 2, v_attrDescr_4859_);
lean_ctor_set_uint8(v___x_4864_, sizeof(void*)*3, v___x_4863_);
lean_inc_ref(v_ext_4860_);
v___x_4865_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_addSimprocAttr___boxed), 8, 2);
lean_closure_set(v___x_4865_, 0, v_attrName_4858_);
lean_closure_set(v___x_4865_, 1, v_ext_4860_);
v___x_4866_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___boxed), 5, 1);
lean_closure_set(v___x_4866_, 0, v_ext_4860_);
v___x_4867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4864_);
lean_ctor_set(v___x_4867_, 1, v___x_4865_);
lean_ctor_set(v___x_4867_, 2, v___x_4866_);
v___x_4868_ = l_Lean_registerBuiltinAttribute(v___x_4867_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr___boxed(lean_object* v_attrName_4869_, lean_object* v_attrDescr_4870_, lean_object* v_ext_4871_, lean_object* v_name_4872_, lean_object* v_a_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l_Lean_Meta_Simp_mkSimprocAttr(v_attrName_4869_, v_attrDescr_4870_, v_ext_4871_, v_name_4872_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4876_ = lean_obj_once(&l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1, &l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1_once, _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs_default___closed__1);
v___x_4877_ = lean_st_mk_ref(v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2____boxed(lean_object* v_a_4879_){
_start:
{
lean_object* v_res_4880_; 
v_res_4880_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_2499117766____hygCtx___hyg_2_();
return v_res_4880_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_registerSimprocAttr___auto__1(void){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = lean_obj_once(&l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26, &l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26_once, _init_l_Lean_Meta_Simp_mkSimprocExt___auto__1___closed__26);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object* v_attrName_4882_, lean_object* v_attrDescr_4883_, lean_object* v_ref_x3f_4884_, lean_object* v_name_4885_){
_start:
{
lean_object* v___x_4887_; 
lean_inc(v_name_4885_);
v___x_4887_ = l_Lean_Meta_Simp_mkSimprocExt(v_name_4885_, v_ref_x3f_4884_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4889_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref(v___x_4887_);
lean_inc(v_a_4888_);
lean_inc(v_attrName_4882_);
v___x_4889_ = l_Lean_Meta_Simp_mkSimprocAttr(v_attrName_4882_, v_attrDescr_4883_, v_a_4888_, v_name_4885_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4900_; 
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4900_ == 0)
{
lean_object* v_unused_4901_; 
v_unused_4901_ = lean_ctor_get(v___x_4889_, 0);
lean_dec(v_unused_4901_);
v___x_4891_ = v___x_4889_;
v_isShared_4892_ = v_isSharedCheck_4900_;
goto v_resetjp_4890_;
}
else
{
lean_dec(v___x_4889_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4900_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4893_ = l_Lean_Meta_Simp_simprocExtensionMapRef;
v___x_4894_ = lean_st_ref_take(v___x_4893_);
lean_inc(v_a_4888_);
v___x_4895_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Simp_registerBuiltinSimprocCore_spec__0___redArg(v___x_4894_, v_attrName_4882_, v_a_4888_);
v___x_4896_ = lean_st_ref_set(v___x_4893_, v___x_4895_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v_a_4888_);
v___x_4898_ = v___x_4891_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4888_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_dec(v_a_4888_);
lean_dec(v_attrName_4882_);
v_a_4902_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4889_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4889_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
else
{
lean_dec(v_name_4885_);
lean_dec_ref(v_attrDescr_4883_);
lean_dec(v_attrName_4882_);
return v___x_4887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr___boxed(lean_object* v_attrName_4910_, lean_object* v_attrDescr_4911_, lean_object* v_ref_x3f_4912_, lean_object* v_name_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Meta_Simp_registerSimprocAttr(v_attrName_4910_, v_attrDescr_4911_, v_ref_x3f_4912_, v_name_4913_);
return v_res_4915_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; 
v___x_4920_ = l_Lean_Meta_Simp_builtinSimprocsRef;
v___x_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4929_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
v___x_4930_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
v___x_4931_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_);
v___x_4932_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
v___x_4933_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_4929_, v___x_4930_, v___x_4931_, v___x_4932_);
return v___x_4933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2____boxed(lean_object* v_a_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_();
return v_res_4935_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = l_Lean_Meta_Simp_builtinSEvalprocsRef;
v___x_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4949_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
v___x_4950_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__2_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
v___x_4951_ = lean_obj_once(&l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_, &l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2__once, _init_l_Lean_Meta_Simp_initFn___closed__3_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_);
v___x_4952_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
v___x_4953_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_4949_, v___x_4950_, v___x_4951_, v___x_4952_);
return v___x_4953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2____boxed(lean_object* v_a_4954_){
_start:
{
lean_object* v_res_4955_; 
v_res_4955_ = l_Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_();
return v_res_4955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4964_ = lean_box(0);
v___x_4965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__4));
v___x_4966_ = l_Lean_mkConst(v___x_4965_, v___x_4964_);
return v___x_4966_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4971_ = lean_box(0);
v___x_4972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__7));
v___x_4973_ = l_Lean_mkConst(v___x_4972_, v___x_4971_);
return v___x_4973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(lean_object* v_addDeclName_4974_, lean_object* v_declName_4975_, uint8_t v___y_4976_, lean_object* v_procExpr_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___y_4987_; 
v___x_4983_ = lean_box(0);
v___x_4984_ = l_Lean_mkConst(v_addDeclName_4974_, v___x_4983_);
lean_inc(v_declName_4975_);
v___x_4985_ = l_Lean_instToExprName___private__1(v_declName_4975_);
if (v___y_4976_ == 0)
{
lean_object* v___x_5007_; 
v___x_5007_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__5);
v___y_4987_ = v___x_5007_;
goto v___jp_4986_;
}
else
{
lean_object* v___x_5008_; 
v___x_5008_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__8);
v___y_4987_ = v___x_5008_;
goto v___jp_4986_;
}
v___jp_4986_:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___closed__1));
v___x_4989_ = l_Lean_Name_append(v_declName_4975_, v___x_4988_);
lean_inc(v___y_4981_);
lean_inc_ref(v___y_4980_);
v___x_4990_ = l_Lean_Core_mkFreshUserName(v___x_4989_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref(v___x_4990_);
v___x_4992_ = lean_unsigned_to_nat(3u);
v___x_4993_ = lean_mk_empty_array_with_capacity(v___x_4992_);
v___x_4994_ = lean_array_push(v___x_4993_, v___x_4985_);
v___x_4995_ = lean_array_push(v___x_4994_, v___y_4987_);
v___x_4996_ = lean_array_push(v___x_4995_, v_procExpr_4977_);
v___x_4997_ = l_Lean_mkAppN(v___x_4984_, v___x_4996_);
lean_dec_ref(v___x_4996_);
v___x_4998_ = l_Lean_declareBuiltin(v_a_4991_, v___x_4997_, v___y_4980_, v___y_4981_);
return v___x_4998_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec_ref(v___y_4987_);
lean_dec_ref(v___x_4985_);
lean_dec_ref(v___x_4984_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec_ref(v_procExpr_4977_);
v_a_4999_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4990_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4990_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed(lean_object* v_addDeclName_5009_, lean_object* v_declName_5010_, lean_object* v___y_5011_, lean_object* v_procExpr_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
uint8_t v___y_4521__boxed_5018_; lean_object* v_res_5019_; 
v___y_4521__boxed_5018_ = lean_unbox(v___y_5011_);
v_res_5019_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(v_addDeclName_5009_, v_declName_5010_, v___y_4521__boxed_5018_, v_procExpr_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(lean_object* v_msg_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_ref_5026_; lean_object* v___x_5027_; lean_object* v_a_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5036_; 
v_ref_5026_ = lean_ctor_get(v___y_5023_, 5);
v___x_5027_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Simp_simprocCore_spec__1_spec__1(v_msg_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5027_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5030_ = v___x_5027_;
v_isShared_5031_ = v_isSharedCheck_5036_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_a_5028_);
lean_dec(v___x_5027_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5036_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v___x_5032_; lean_object* v___x_5034_; 
lean_inc(v_ref_5026_);
v___x_5032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5032_, 0, v_ref_5026_);
lean_ctor_set(v___x_5032_, 1, v_a_5028_);
if (v_isShared_5031_ == 0)
{
lean_ctor_set_tag(v___x_5030_, 1);
lean_ctor_set(v___x_5030_, 0, v___x_5032_);
v___x_5034_ = v___x_5030_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg___boxed(lean_object* v_msg_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_res_5043_; 
v_res_5043_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v_msg_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
lean_dec(v___y_5041_);
lean_dec_ref(v___y_5040_);
lean_dec(v___y_5039_);
lean_dec_ref(v___y_5038_);
return v_res_5043_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; 
v___x_5045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__0));
v___x_5046_ = l_Lean_stringToMessageData(v___x_5045_);
return v___x_5046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3(void){
_start:
{
uint8_t v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5052_ = 0;
v___x_5053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2));
v___x_5054_ = l_Lean_MessageData_ofConstName(v___x_5053_, v___x_5052_);
return v___x_5054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4(void){
_start:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5055_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__3);
v___x_5056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__1);
v___x_5057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5056_);
lean_ctor_set(v___x_5057_, 1, v___x_5055_);
return v___x_5057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; 
v___x_5059_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__5));
v___x_5060_ = l_Lean_stringToMessageData(v___x_5059_);
return v___x_5060_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__6);
v___x_5062_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__4);
v___x_5063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5063_, 0, v___x_5062_);
lean_ctor_set(v___x_5063_, 1, v___x_5061_);
return v___x_5063_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9(void){
_start:
{
uint8_t v___x_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5069_ = 0;
v___x_5070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8));
v___x_5071_ = l_Lean_MessageData_ofConstName(v___x_5070_, v___x_5069_);
return v___x_5071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10(void){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__9);
v___x_5073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__7);
v___x_5074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5074_, 0, v___x_5073_);
lean_ctor_set(v___x_5074_, 1, v___x_5072_);
return v___x_5074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12(void){
_start:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; 
v___x_5076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__11));
v___x_5077_ = l_Lean_stringToMessageData(v___x_5076_);
return v___x_5077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; 
v___x_5078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__12);
v___x_5079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__10);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5079_);
lean_ctor_set(v___x_5080_, 1, v___x_5078_);
return v___x_5080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15(void){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__14));
v___x_5083_ = l_Lean_stringToMessageData(v___x_5082_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(lean_object* v_declName_5084_, lean_object* v___f_5085_, lean_object* v_tp_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
uint8_t v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
v___x_5092_ = 0;
v___x_5093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__13);
v___x_5094_ = l_Lean_MessageData_ofConstName(v_declName_5084_, v___x_5092_);
v___x_5095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5093_);
lean_ctor_set(v___x_5095_, 1, v___x_5094_);
v___x_5096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__15);
v___x_5097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5097_, 0, v___x_5095_);
lean_ctor_set(v___x_5097_, 1, v___x_5096_);
v___x_5098_ = l_Lean_indentExpr(v_tp_5086_);
v___x_5099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v___x_5099_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___boxed(lean_object* v_declName_5109_, lean_object* v___f_5110_, lean_object* v_tp_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_){
_start:
{
lean_object* v_res_5117_; 
v_res_5117_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5109_, v___f_5110_, v_tp_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
lean_dec(v___y_5115_);
lean_dec_ref(v___y_5114_);
lean_dec(v___y_5113_);
lean_dec_ref(v___y_5112_);
lean_dec_ref(v___f_5110_);
return v_res_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_5118_, lean_object* v_msg_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
lean_object* v_fileName_5125_; lean_object* v_fileMap_5126_; lean_object* v_options_5127_; lean_object* v_currRecDepth_5128_; lean_object* v_maxRecDepth_5129_; lean_object* v_ref_5130_; lean_object* v_currNamespace_5131_; lean_object* v_openDecls_5132_; lean_object* v_initHeartbeats_5133_; lean_object* v_maxHeartbeats_5134_; lean_object* v_quotContext_5135_; lean_object* v_currMacroScope_5136_; uint8_t v_diag_5137_; lean_object* v_cancelTk_x3f_5138_; uint8_t v_suppressElabErrors_5139_; lean_object* v_inheritedTraceOptions_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5149_; 
v_fileName_5125_ = lean_ctor_get(v___y_5122_, 0);
v_fileMap_5126_ = lean_ctor_get(v___y_5122_, 1);
v_options_5127_ = lean_ctor_get(v___y_5122_, 2);
v_currRecDepth_5128_ = lean_ctor_get(v___y_5122_, 3);
v_maxRecDepth_5129_ = lean_ctor_get(v___y_5122_, 4);
v_ref_5130_ = lean_ctor_get(v___y_5122_, 5);
v_currNamespace_5131_ = lean_ctor_get(v___y_5122_, 6);
v_openDecls_5132_ = lean_ctor_get(v___y_5122_, 7);
v_initHeartbeats_5133_ = lean_ctor_get(v___y_5122_, 8);
v_maxHeartbeats_5134_ = lean_ctor_get(v___y_5122_, 9);
v_quotContext_5135_ = lean_ctor_get(v___y_5122_, 10);
v_currMacroScope_5136_ = lean_ctor_get(v___y_5122_, 11);
v_diag_5137_ = lean_ctor_get_uint8(v___y_5122_, sizeof(void*)*14);
v_cancelTk_x3f_5138_ = lean_ctor_get(v___y_5122_, 12);
v_suppressElabErrors_5139_ = lean_ctor_get_uint8(v___y_5122_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5140_ = lean_ctor_get(v___y_5122_, 13);
v_isSharedCheck_5149_ = !lean_is_exclusive(v___y_5122_);
if (v_isSharedCheck_5149_ == 0)
{
v___x_5142_ = v___y_5122_;
v_isShared_5143_ = v_isSharedCheck_5149_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_inheritedTraceOptions_5140_);
lean_inc(v_cancelTk_x3f_5138_);
lean_inc(v_currMacroScope_5136_);
lean_inc(v_quotContext_5135_);
lean_inc(v_maxHeartbeats_5134_);
lean_inc(v_initHeartbeats_5133_);
lean_inc(v_openDecls_5132_);
lean_inc(v_currNamespace_5131_);
lean_inc(v_ref_5130_);
lean_inc(v_maxRecDepth_5129_);
lean_inc(v_currRecDepth_5128_);
lean_inc(v_options_5127_);
lean_inc(v_fileMap_5126_);
lean_inc(v_fileName_5125_);
lean_dec(v___y_5122_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5149_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v_ref_5144_; lean_object* v___x_5146_; 
v_ref_5144_ = l_Lean_replaceRef(v_ref_5118_, v_ref_5130_);
lean_dec(v_ref_5130_);
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 5, v_ref_5144_);
v___x_5146_ = v___x_5142_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5148_; 
v_reuseFailAlloc_5148_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_fileName_5125_);
lean_ctor_set(v_reuseFailAlloc_5148_, 1, v_fileMap_5126_);
lean_ctor_set(v_reuseFailAlloc_5148_, 2, v_options_5127_);
lean_ctor_set(v_reuseFailAlloc_5148_, 3, v_currRecDepth_5128_);
lean_ctor_set(v_reuseFailAlloc_5148_, 4, v_maxRecDepth_5129_);
lean_ctor_set(v_reuseFailAlloc_5148_, 5, v_ref_5144_);
lean_ctor_set(v_reuseFailAlloc_5148_, 6, v_currNamespace_5131_);
lean_ctor_set(v_reuseFailAlloc_5148_, 7, v_openDecls_5132_);
lean_ctor_set(v_reuseFailAlloc_5148_, 8, v_initHeartbeats_5133_);
lean_ctor_set(v_reuseFailAlloc_5148_, 9, v_maxHeartbeats_5134_);
lean_ctor_set(v_reuseFailAlloc_5148_, 10, v_quotContext_5135_);
lean_ctor_set(v_reuseFailAlloc_5148_, 11, v_currMacroScope_5136_);
lean_ctor_set(v_reuseFailAlloc_5148_, 12, v_cancelTk_x3f_5138_);
lean_ctor_set(v_reuseFailAlloc_5148_, 13, v_inheritedTraceOptions_5140_);
lean_ctor_set_uint8(v_reuseFailAlloc_5148_, sizeof(void*)*14, v_diag_5137_);
lean_ctor_set_uint8(v_reuseFailAlloc_5148_, sizeof(void*)*14 + 1, v_suppressElabErrors_5139_);
v___x_5146_ = v_reuseFailAlloc_5148_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v_msg_5119_, v___y_5120_, v___y_5121_, v___x_5146_, v___y_5123_);
lean_dec_ref(v___x_5146_);
return v___x_5147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_5150_, lean_object* v_msg_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v_res_5157_; 
v_res_5157_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5150_, v_msg_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec(v_ref_5150_);
return v_res_5157_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_5159_; lean_object* v___x_5160_; 
v___x_5159_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__0));
v___x_5160_ = l_Lean_stringToMessageData(v___x_5159_);
return v___x_5160_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_5162_; lean_object* v___x_5163_; 
v___x_5162_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__2));
v___x_5163_ = l_Lean_stringToMessageData(v___x_5162_);
return v___x_5163_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__4));
v___x_5166_ = l_Lean_stringToMessageData(v___x_5165_);
return v___x_5166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_5168_; lean_object* v___x_5169_; 
v___x_5168_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_5169_ = l_Lean_stringToMessageData(v___x_5168_);
return v___x_5169_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; 
v___x_5171_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_5172_ = l_Lean_stringToMessageData(v___x_5171_);
return v___x_5172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_5175_ = l_Lean_stringToMessageData(v___x_5174_);
return v___x_5175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_5177_; lean_object* v___x_5178_; 
v___x_5177_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_5178_ = l_Lean_stringToMessageData(v___x_5177_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_5179_, lean_object* v_declHint_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v___x_5183_; lean_object* v_env_5184_; uint8_t v___x_5185_; 
v___x_5183_ = lean_st_ref_get(v___y_5181_);
v_env_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc_ref(v_env_5184_);
lean_dec(v___x_5183_);
v___x_5185_ = l_Lean_Name_isAnonymous(v_declHint_5180_);
if (v___x_5185_ == 0)
{
uint8_t v_isExporting_5186_; 
v_isExporting_5186_ = lean_ctor_get_uint8(v_env_5184_, sizeof(void*)*8);
if (v_isExporting_5186_ == 0)
{
lean_object* v___x_5187_; 
lean_dec_ref(v_env_5184_);
lean_dec(v_declHint_5180_);
v___x_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5187_, 0, v_msg_5179_);
return v___x_5187_;
}
else
{
lean_object* v___x_5188_; uint8_t v___x_5189_; 
lean_inc_ref(v_env_5184_);
v___x_5188_ = l_Lean_Environment_setExporting(v_env_5184_, v___x_5185_);
lean_inc(v_declHint_5180_);
lean_inc_ref(v___x_5188_);
v___x_5189_ = l_Lean_Environment_contains(v___x_5188_, v_declHint_5180_, v_isExporting_5186_);
if (v___x_5189_ == 0)
{
lean_object* v___x_5190_; 
lean_dec_ref(v___x_5188_);
lean_dec_ref(v_env_5184_);
lean_dec(v_declHint_5180_);
v___x_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5190_, 0, v_msg_5179_);
return v___x_5190_;
}
else
{
lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v_c_5196_; lean_object* v___x_5197_; 
v___x_5191_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__2);
v___x_5192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__5);
v___x_5193_ = l_Lean_Options_empty;
v___x_5194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5194_, 0, v___x_5188_);
lean_ctor_set(v___x_5194_, 1, v___x_5191_);
lean_ctor_set(v___x_5194_, 2, v___x_5192_);
lean_ctor_set(v___x_5194_, 3, v___x_5193_);
lean_inc(v_declHint_5180_);
v___x_5195_ = l_Lean_MessageData_ofConstName(v_declHint_5180_, v___x_5185_);
v_c_5196_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_5196_, 0, v___x_5194_);
lean_ctor_set(v_c_5196_, 1, v___x_5195_);
v___x_5197_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5184_, v_declHint_5180_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; 
lean_dec_ref(v_env_5184_);
lean_dec(v_declHint_5180_);
v___x_5198_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_5199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
lean_ctor_set(v___x_5199_, 1, v_c_5196_);
v___x_5200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_5201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5199_);
lean_ctor_set(v___x_5201_, 1, v___x_5200_);
v___x_5202_ = l_Lean_MessageData_note(v___x_5201_);
v___x_5203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5203_, 0, v_msg_5179_);
lean_ctor_set(v___x_5203_, 1, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5203_);
return v___x_5204_;
}
else
{
lean_object* v_val_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5240_; 
v_val_5205_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5240_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5240_ == 0)
{
v___x_5207_ = v___x_5197_;
v_isShared_5208_ = v_isSharedCheck_5240_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_val_5205_);
lean_dec(v___x_5197_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5240_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v_mod_5212_; uint8_t v___x_5213_; 
v___x_5209_ = lean_box(0);
v___x_5210_ = l_Lean_Environment_header(v_env_5184_);
lean_dec_ref(v_env_5184_);
v___x_5211_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5210_);
v_mod_5212_ = lean_array_get(v___x_5209_, v___x_5211_, v_val_5205_);
lean_dec(v_val_5205_);
lean_dec_ref(v___x_5211_);
v___x_5213_ = l_Lean_isPrivateName(v_declHint_5180_);
lean_dec(v_declHint_5180_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5225_; 
v___x_5214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_5215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5215_, 0, v___x_5214_);
lean_ctor_set(v___x_5215_, 1, v_c_5196_);
v___x_5216_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_5217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5215_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = l_Lean_MessageData_ofName(v_mod_5212_);
v___x_5219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5217_);
lean_ctor_set(v___x_5219_, 1, v___x_5218_);
v___x_5220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_5221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5221_, 0, v___x_5219_);
lean_ctor_set(v___x_5221_, 1, v___x_5220_);
v___x_5222_ = l_Lean_MessageData_note(v___x_5221_);
v___x_5223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5223_, 0, v_msg_5179_);
lean_ctor_set(v___x_5223_, 1, v___x_5222_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set_tag(v___x_5207_, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5223_);
v___x_5225_ = v___x_5207_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
else
{
lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5238_; 
v___x_5227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_5228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5228_, 0, v___x_5227_);
lean_ctor_set(v___x_5228_, 1, v_c_5196_);
v___x_5229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_5230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5228_);
lean_ctor_set(v___x_5230_, 1, v___x_5229_);
v___x_5231_ = l_Lean_MessageData_ofName(v_mod_5212_);
v___x_5232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5232_, 0, v___x_5230_);
lean_ctor_set(v___x_5232_, 1, v___x_5231_);
v___x_5233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_5234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5234_, 0, v___x_5232_);
lean_ctor_set(v___x_5234_, 1, v___x_5233_);
v___x_5235_ = l_Lean_MessageData_note(v___x_5234_);
v___x_5236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5236_, 0, v_msg_5179_);
lean_ctor_set(v___x_5236_, 1, v___x_5235_);
if (v_isShared_5208_ == 0)
{
lean_ctor_set_tag(v___x_5207_, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5236_);
v___x_5238_ = v___x_5207_;
goto v_reusejp_5237_;
}
else
{
lean_object* v_reuseFailAlloc_5239_; 
v_reuseFailAlloc_5239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5239_, 0, v___x_5236_);
v___x_5238_ = v_reuseFailAlloc_5239_;
goto v_reusejp_5237_;
}
v_reusejp_5237_:
{
return v___x_5238_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5241_; 
lean_dec_ref(v_env_5184_);
lean_dec(v_declHint_5180_);
v___x_5241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5241_, 0, v_msg_5179_);
return v___x_5241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_5242_, lean_object* v_declHint_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5242_, v_declHint_5243_, v___y_5244_);
lean_dec(v___y_5244_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_5247_, lean_object* v_declHint_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_){
_start:
{
lean_object* v___x_5254_; lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5264_; 
v___x_5254_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5247_, v_declHint_5248_, v___y_5252_);
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5257_ = v___x_5254_;
v_isShared_5258_ = v_isSharedCheck_5264_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5254_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5264_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5259_ = l_Lean_unknownIdentifierMessageTag;
v___x_5260_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_5260_, 0, v___x_5259_);
lean_ctor_set(v___x_5260_, 1, v_a_5255_);
if (v_isShared_5258_ == 0)
{
lean_ctor_set(v___x_5257_, 0, v___x_5260_);
v___x_5262_ = v___x_5257_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_5265_, lean_object* v_declHint_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(v_msg_5265_, v_declHint_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
return v_res_5272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_5273_, lean_object* v_msg_5274_, lean_object* v_declHint_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_){
_start:
{
lean_object* v___x_5281_; lean_object* v_a_5282_; lean_object* v___x_5283_; 
v___x_5281_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4(v_msg_5274_, v_declHint_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_a_5282_);
lean_dec_ref(v___x_5281_);
v___x_5283_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5273_, v_a_5282_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_5284_, lean_object* v_msg_5285_, lean_object* v_declHint_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_5284_, v_msg_5285_, v_declHint_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_);
lean_dec(v___y_5290_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec(v_ref_5284_);
return v_res_5292_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; 
v___x_5293_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__0));
v___x_5294_ = l_Lean_stringToMessageData(v___x_5293_);
return v___x_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(lean_object* v_ref_5295_, lean_object* v_constName_5296_, lean_object* v___y_5297_, lean_object* v___y_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_){
_start:
{
lean_object* v___x_5302_; uint8_t v___x_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5302_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_5303_ = 0;
lean_inc(v_constName_5296_);
v___x_5304_ = l_Lean_MessageData_ofConstName(v_constName_5296_, v___x_5303_);
v___x_5305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5305_, 0, v___x_5302_);
lean_ctor_set(v___x_5305_, 1, v___x_5304_);
v___x_5306_ = lean_obj_once(&l_Lean_Meta_Simp_eraseSimprocAttr___closed__0, &l_Lean_Meta_Simp_eraseSimprocAttr___closed__0_once, _init_l_Lean_Meta_Simp_eraseSimprocAttr___closed__0);
v___x_5307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5305_);
lean_ctor_set(v___x_5307_, 1, v___x_5306_);
v___x_5308_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_5295_, v___x_5307_, v_constName_5296_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
return v___x_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_ref_5309_, lean_object* v_constName_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_){
_start:
{
lean_object* v_res_5316_; 
v_res_5316_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(v_ref_5309_, v_constName_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
lean_dec(v___y_5314_);
lean_dec(v___y_5312_);
lean_dec_ref(v___y_5311_);
lean_dec(v_ref_5309_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(lean_object* v_constName_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_ref_5323_; lean_object* v___x_5324_; 
v_ref_5323_ = lean_ctor_get(v___y_5320_, 5);
lean_inc(v_ref_5323_);
v___x_5324_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(v_ref_5323_, v_constName_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_);
lean_dec(v_ref_5323_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg___boxed(lean_object* v_constName_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v_res_5331_; 
v_res_5331_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(v_constName_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
lean_dec(v___y_5329_);
lean_dec(v___y_5327_);
lean_dec_ref(v___y_5326_);
return v_res_5331_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(lean_object* v_constName_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v___x_5338_; lean_object* v_env_5339_; uint8_t v___x_5340_; lean_object* v___x_5341_; 
v___x_5338_ = lean_st_ref_get(v___y_5336_);
v_env_5339_ = lean_ctor_get(v___x_5338_, 0);
lean_inc_ref(v_env_5339_);
lean_dec(v___x_5338_);
v___x_5340_ = 0;
lean_inc(v_constName_5332_);
v___x_5341_ = l_Lean_Environment_find_x3f(v_env_5339_, v_constName_5332_, v___x_5340_);
if (lean_obj_tag(v___x_5341_) == 0)
{
lean_object* v___x_5342_; 
v___x_5342_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(v_constName_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
return v___x_5342_;
}
else
{
lean_object* v_val_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec_ref(v___y_5335_);
lean_dec(v_constName_5332_);
v_val_5343_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5341_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_val_5343_);
lean_dec(v___x_5341_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set_tag(v___x_5345_, 0);
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_val_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1___boxed(lean_object* v_constName_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(v_constName_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
return v_res_5357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0(void){
_start:
{
lean_object* v___x_5358_; 
v___x_5358_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1(void){
_start:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__0);
v___x_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5360_, 0, v___x_5359_);
return v___x_5360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2(void){
_start:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; 
v___x_5361_ = lean_box(1);
v___x_5362_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4);
v___x_5363_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1);
v___x_5364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5364_, 0, v___x_5363_);
lean_ctor_set(v___x_5364_, 1, v___x_5362_);
lean_ctor_set(v___x_5364_, 2, v___x_5361_);
return v___x_5364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4(void){
_start:
{
uint8_t v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; uint8_t v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; 
v___x_5367_ = 1;
v___x_5368_ = lean_unsigned_to_nat(0u);
v___x_5369_ = lean_box(0);
v___x_5370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__3));
v___x_5371_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__2);
v___x_5372_ = lean_box(1);
v___x_5373_ = 0;
v___x_5374_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_5375_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5375_, 0, v___x_5374_);
lean_ctor_set(v___x_5375_, 1, v___x_5372_);
lean_ctor_set(v___x_5375_, 2, v___x_5371_);
lean_ctor_set(v___x_5375_, 3, v___x_5370_);
lean_ctor_set(v___x_5375_, 4, v___x_5369_);
lean_ctor_set(v___x_5375_, 5, v___x_5368_);
lean_ctor_set(v___x_5375_, 6, v___x_5369_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*7, v___x_5373_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*7 + 1, v___x_5373_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*7 + 2, v___x_5373_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*7 + 3, v___x_5367_);
return v___x_5375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___x_5378_; 
v___x_5376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1);
v___x_5377_ = lean_unsigned_to_nat(0u);
v___x_5378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_5378_, 0, v___x_5377_);
lean_ctor_set(v___x_5378_, 1, v___x_5377_);
lean_ctor_set(v___x_5378_, 2, v___x_5377_);
lean_ctor_set(v___x_5378_, 3, v___x_5376_);
lean_ctor_set(v___x_5378_, 4, v___x_5376_);
lean_ctor_set(v___x_5378_, 5, v___x_5376_);
lean_ctor_set(v___x_5378_, 6, v___x_5376_);
lean_ctor_set(v___x_5378_, 7, v___x_5376_);
lean_ctor_set(v___x_5378_, 8, v___x_5376_);
return v___x_5378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6(void){
_start:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; 
v___x_5379_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1);
v___x_5380_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5379_);
lean_ctor_set(v___x_5380_, 1, v___x_5379_);
lean_ctor_set(v___x_5380_, 2, v___x_5379_);
lean_ctor_set(v___x_5380_, 3, v___x_5379_);
lean_ctor_set(v___x_5380_, 4, v___x_5379_);
lean_ctor_set(v___x_5380_, 5, v___x_5379_);
return v___x_5380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7(void){
_start:
{
lean_object* v___x_5381_; lean_object* v___x_5382_; 
v___x_5381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__1);
v___x_5382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5382_, 0, v___x_5381_);
lean_ctor_set(v___x_5382_, 1, v___x_5381_);
lean_ctor_set(v___x_5382_, 2, v___x_5381_);
lean_ctor_set(v___x_5382_, 3, v___x_5381_);
lean_ctor_set(v___x_5382_, 4, v___x_5381_);
return v___x_5382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8(void){
_start:
{
lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; 
v___x_5383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__7);
v___x_5384_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0_spec__0___closed__4);
v___x_5385_ = lean_box(1);
v___x_5386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__6);
v___x_5387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__5);
v___x_5388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5388_, 0, v___x_5387_);
lean_ctor_set(v___x_5388_, 1, v___x_5386_);
lean_ctor_set(v___x_5388_, 2, v___x_5385_);
lean_ctor_set(v___x_5388_, 3, v___x_5384_);
lean_ctor_set(v___x_5388_, 4, v___x_5383_);
return v___x_5388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12(void){
_start:
{
lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5394_ = lean_unsigned_to_nat(0u);
v___x_5395_ = l_Lean_Level_ofNat(v___x_5394_);
return v___x_5395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13(void){
_start:
{
lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
v___x_5396_ = lean_box(0);
v___x_5397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12);
v___x_5398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5397_);
lean_ctor_set(v___x_5398_, 1, v___x_5396_);
return v___x_5398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14(void){
_start:
{
lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__13);
v___x_5400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__12);
v___x_5401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5400_);
lean_ctor_set(v___x_5401_, 1, v___x_5399_);
return v___x_5401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15(void){
_start:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; 
v___x_5402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14);
v___x_5403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__11));
v___x_5404_ = l_Lean_mkConst(v___x_5403_, v___x_5402_);
return v___x_5404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16(void){
_start:
{
lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5405_ = lean_box(0);
v___x_5406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__2));
v___x_5407_ = l_Lean_mkConst(v___x_5406_, v___x_5405_);
return v___x_5407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17(void){
_start:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5408_ = lean_box(0);
v___x_5409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___closed__8));
v___x_5410_ = l_Lean_mkConst(v___x_5409_, v___x_5408_);
return v___x_5410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20(void){
_start:
{
lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; 
v___x_5415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__14);
v___x_5416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__19));
v___x_5417_ = l_Lean_mkConst(v___x_5416_, v___x_5415_);
return v___x_5417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object* v_declName_5418_, lean_object* v_stx_5419_, lean_object* v_addDeclName_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_){
_start:
{
lean_object* v___y_5425_; lean_object* v___y_5426_; lean_object* v___x_5436_; lean_object* v___x_5437_; uint8_t v___x_5438_; uint8_t v___x_5439_; uint8_t v___y_5441_; 
v___x_5436_ = lean_unsigned_to_nat(1u);
v___x_5437_ = l_Lean_Syntax_getArg(v_stx_5419_, v___x_5436_);
v___x_5438_ = l_Lean_Syntax_isNone(v___x_5437_);
v___x_5439_ = 1;
if (v___x_5438_ == 0)
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; uint8_t v___x_5521_; 
v___x_5517_ = lean_unsigned_to_nat(0u);
v___x_5518_ = l_Lean_Syntax_getArg(v___x_5437_, v___x_5517_);
lean_dec(v___x_5437_);
v___x_5519_ = l_Lean_Syntax_getKind(v___x_5518_);
v___x_5520_ = ((lean_object*)(l_Lean_Meta_Simp_addSimprocAttr___closed__6));
v___x_5521_ = lean_name_eq(v___x_5519_, v___x_5520_);
lean_dec(v___x_5519_);
v___y_5441_ = v___x_5521_;
goto v___jp_5440_;
}
else
{
lean_dec(v___x_5437_);
v___y_5441_ = v___x_5439_;
goto v___jp_5440_;
}
v___jp_5424_:
{
if (lean_obj_tag(v___y_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5435_; 
v_a_5427_ = lean_ctor_get(v___y_5426_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___y_5426_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5429_ = v___y_5426_;
v_isShared_5430_ = v_isSharedCheck_5435_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v___y_5426_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5435_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5431_; lean_object* v___x_5433_; 
v___x_5431_ = lean_st_ref_get(v___y_5425_);
lean_dec(v___y_5425_);
lean_dec(v___x_5431_);
if (v_isShared_5430_ == 0)
{
v___x_5433_ = v___x_5429_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5427_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
else
{
lean_dec(v___y_5425_);
return v___y_5426_;
}
}
v___jp_5440_:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; 
v___x_5442_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__4);
v___x_5443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__8);
v___x_5444_ = lean_st_mk_ref(v___x_5443_);
lean_inc_ref(v_a_5421_);
lean_inc(v_declName_5418_);
v___x_5445_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1(v_declName_5418_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v_a_5446_; lean_object* v___x_5447_; lean_object* v___f_5448_; lean_object* v___x_5449_; 
v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_a_5446_);
lean_dec_ref(v___x_5445_);
v___x_5447_ = lean_box(v___y_5441_);
lean_inc(v_declName_5418_);
lean_inc(v_addDeclName_5420_);
v___f_5448_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed), 9, 3);
lean_closure_set(v___f_5448_, 0, v_addDeclName_5420_);
lean_closure_set(v___f_5448_, 1, v_declName_5418_);
lean_closure_set(v___f_5448_, 2, v___x_5447_);
v___x_5449_ = l_Lean_ConstantInfo_type(v_a_5446_);
lean_dec(v_a_5446_);
if (lean_obj_tag(v___x_5449_) == 4)
{
lean_object* v_declName_5450_; 
v_declName_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_declName_5450_);
if (lean_obj_tag(v_declName_5450_) == 1)
{
lean_object* v_pre_5451_; 
v_pre_5451_ = lean_ctor_get(v_declName_5450_, 0);
lean_inc(v_pre_5451_);
if (lean_obj_tag(v_pre_5451_) == 1)
{
lean_object* v_pre_5452_; 
v_pre_5452_ = lean_ctor_get(v_pre_5451_, 0);
lean_inc(v_pre_5452_);
if (lean_obj_tag(v_pre_5452_) == 1)
{
lean_object* v_pre_5453_; 
v_pre_5453_ = lean_ctor_get(v_pre_5452_, 0);
lean_inc(v_pre_5453_);
if (lean_obj_tag(v_pre_5453_) == 1)
{
lean_object* v_pre_5454_; 
v_pre_5454_ = lean_ctor_get(v_pre_5453_, 0);
lean_inc(v_pre_5454_);
if (lean_obj_tag(v_pre_5454_) == 0)
{
lean_object* v_us_5455_; lean_object* v_str_5456_; lean_object* v_str_5457_; lean_object* v_str_5458_; lean_object* v_str_5459_; lean_object* v___x_5460_; uint8_t v___x_5461_; 
v_us_5455_ = lean_ctor_get(v___x_5449_, 1);
lean_inc(v_us_5455_);
v_str_5456_ = lean_ctor_get(v_declName_5450_, 1);
lean_inc_ref(v_str_5456_);
lean_dec_ref(v_declName_5450_);
v_str_5457_ = lean_ctor_get(v_pre_5451_, 1);
lean_inc_ref(v_str_5457_);
lean_dec_ref(v_pre_5451_);
v_str_5458_ = lean_ctor_get(v_pre_5452_, 1);
lean_inc_ref(v_str_5458_);
lean_dec_ref(v_pre_5452_);
v_str_5459_ = lean_ctor_get(v_pre_5453_, 1);
lean_inc_ref(v_str_5459_);
lean_dec_ref(v_pre_5453_);
v___x_5460_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__5_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_5461_ = lean_string_dec_eq(v_str_5459_, v___x_5460_);
lean_dec_ref(v_str_5459_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5462_; 
lean_dec_ref(v_str_5458_);
lean_dec_ref(v_str_5457_);
lean_dec_ref(v_str_5456_);
lean_dec(v_us_5455_);
lean_dec(v_addDeclName_5420_);
v___x_5462_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5462_;
goto v___jp_5424_;
}
else
{
lean_object* v___x_5463_; uint8_t v___x_5464_; 
lean_dec_ref(v___x_5449_);
v___x_5463_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__6_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_5464_ = lean_string_dec_eq(v_str_5458_, v___x_5463_);
if (v___x_5464_ == 0)
{
lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
lean_dec(v_addDeclName_5420_);
v___x_5465_ = l_Lean_Name_str___override(v_pre_5454_, v___x_5460_);
v___x_5466_ = l_Lean_Name_str___override(v___x_5465_, v_str_5458_);
v___x_5467_ = l_Lean_Name_str___override(v___x_5466_, v_str_5457_);
v___x_5468_ = l_Lean_Name_str___override(v___x_5467_, v_str_5456_);
v___x_5469_ = l_Lean_Expr_const___override(v___x_5468_, v_us_5455_);
v___x_5470_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5469_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5470_;
goto v___jp_5424_;
}
else
{
lean_object* v___x_5471_; uint8_t v___x_5472_; 
lean_dec_ref(v_str_5458_);
v___x_5471_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__7_00___x40_Lean_Meta_Tactic_Simp_Simproc_1881898657____hygCtx___hyg_2_));
v___x_5472_ = lean_string_dec_eq(v_str_5457_, v___x_5471_);
if (v___x_5472_ == 0)
{
lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
lean_dec(v_addDeclName_5420_);
v___x_5473_ = l_Lean_Name_str___override(v_pre_5454_, v___x_5460_);
v___x_5474_ = l_Lean_Name_str___override(v___x_5473_, v___x_5463_);
v___x_5475_ = l_Lean_Name_str___override(v___x_5474_, v_str_5457_);
v___x_5476_ = l_Lean_Name_str___override(v___x_5475_, v_str_5456_);
v___x_5477_ = l_Lean_Expr_const___override(v___x_5476_, v_us_5455_);
v___x_5478_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5477_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5478_;
goto v___jp_5424_;
}
else
{
lean_object* v___x_5479_; uint8_t v___x_5480_; 
lean_dec_ref(v_str_5457_);
v___x_5479_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__4));
v___x_5480_ = lean_string_dec_eq(v_str_5456_, v___x_5479_);
if (v___x_5480_ == 0)
{
lean_object* v___x_5481_; uint8_t v___x_5482_; 
v___x_5481_ = ((lean_object*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___closed__5));
v___x_5482_ = lean_string_dec_eq(v_str_5456_, v___x_5481_);
if (v___x_5482_ == 0)
{
lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
lean_dec(v_addDeclName_5420_);
v___x_5483_ = l_Lean_Name_str___override(v_pre_5454_, v___x_5460_);
v___x_5484_ = l_Lean_Name_str___override(v___x_5483_, v___x_5463_);
v___x_5485_ = l_Lean_Name_str___override(v___x_5484_, v___x_5471_);
v___x_5486_ = l_Lean_Name_str___override(v___x_5485_, v_str_5456_);
v___x_5487_ = l_Lean_Expr_const___override(v___x_5486_, v_us_5455_);
v___x_5488_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5487_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5488_;
goto v___jp_5424_;
}
else
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
lean_dec_ref(v_str_5456_);
lean_dec(v_us_5455_);
lean_dec_ref(v___f_5448_);
v___x_5489_ = lean_box(0);
v___x_5490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__15);
v___x_5491_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16);
v___x_5492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17);
lean_inc(v_declName_5418_);
v___x_5493_ = l_Lean_mkConst(v_declName_5418_, v___x_5489_);
v___x_5494_ = l_Lean_mkApp3(v___x_5490_, v___x_5491_, v___x_5492_, v___x_5493_);
v___x_5495_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(v_addDeclName_5420_, v_declName_5418_, v___y_5441_, v___x_5494_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5495_;
goto v___jp_5424_;
}
}
else
{
lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; 
lean_dec_ref(v_str_5456_);
lean_dec(v_us_5455_);
lean_dec_ref(v___f_5448_);
v___x_5496_ = lean_box(0);
v___x_5497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__20);
v___x_5498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__16);
v___x_5499_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17_once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___closed__17);
lean_inc(v_declName_5418_);
v___x_5500_ = l_Lean_mkConst(v_declName_5418_, v___x_5496_);
v___x_5501_ = l_Lean_mkApp3(v___x_5497_, v___x_5498_, v___x_5499_, v___x_5500_);
v___x_5502_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(v_addDeclName_5420_, v_declName_5418_, v___y_5441_, v___x_5501_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5502_;
goto v___jp_5424_;
}
}
}
}
}
else
{
lean_object* v___x_5503_; 
lean_dec(v_pre_5454_);
lean_dec_ref(v_pre_5453_);
lean_dec_ref(v_pre_5452_);
lean_dec_ref(v_pre_5451_);
lean_dec_ref(v_declName_5450_);
lean_dec(v_addDeclName_5420_);
v___x_5503_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5503_;
goto v___jp_5424_;
}
}
else
{
lean_object* v___x_5504_; 
lean_dec_ref(v_pre_5452_);
lean_dec(v_pre_5453_);
lean_dec_ref(v_pre_5451_);
lean_dec_ref(v_declName_5450_);
lean_dec(v_addDeclName_5420_);
v___x_5504_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5504_;
goto v___jp_5424_;
}
}
else
{
lean_object* v___x_5505_; 
lean_dec(v_pre_5452_);
lean_dec_ref(v_pre_5451_);
lean_dec_ref(v_declName_5450_);
lean_dec(v_addDeclName_5420_);
v___x_5505_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5505_;
goto v___jp_5424_;
}
}
else
{
lean_object* v___x_5506_; 
lean_dec_ref(v_declName_5450_);
lean_dec(v_pre_5451_);
lean_dec(v_addDeclName_5420_);
v___x_5506_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5506_;
goto v___jp_5424_;
}
}
else
{
lean_object* v___x_5507_; 
lean_dec(v_declName_5450_);
lean_dec(v_addDeclName_5420_);
v___x_5507_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5507_;
goto v___jp_5424_;
}
}
else
{
lean_object* v___x_5508_; 
lean_dec(v_addDeclName_5420_);
v___x_5508_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(v_declName_5418_, v___f_5448_, v___x_5449_, v___x_5442_, v___x_5444_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec_ref(v___f_5448_);
v___y_5425_ = v___x_5444_;
v___y_5426_ = v___x_5508_;
goto v___jp_5424_;
}
}
else
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5516_; 
lean_dec(v___x_5444_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_addDeclName_5420_);
lean_dec(v_declName_5418_);
v_a_5509_ = lean_ctor_get(v___x_5445_, 0);
v_isSharedCheck_5516_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5516_ == 0)
{
v___x_5511_ = v___x_5445_;
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5445_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5516_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v___x_5514_; 
if (v_isShared_5512_ == 0)
{
v___x_5514_ = v___x_5511_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_a_5509_);
v___x_5514_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
return v___x_5514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object* v_declName_5522_, lean_object* v_stx_5523_, lean_object* v_addDeclName_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_){
_start:
{
lean_object* v_res_5528_; 
v_res_5528_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(v_declName_5522_, v_stx_5523_, v_addDeclName_5524_, v_a_5525_, v_a_5526_);
lean_dec(v_stx_5523_);
return v_res_5528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0(lean_object* v_00_u03b1_5529_, lean_object* v_msg_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
lean_object* v___x_5536_; 
v___x_5536_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___redArg(v_msg_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
return v___x_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0___boxed(lean_object* v_00_u03b1_5537_, lean_object* v_msg_5538_, lean_object* v___y_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_){
_start:
{
lean_object* v_res_5544_; 
v_res_5544_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__0(v_00_u03b1_5537_, v_msg_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec(v___y_5540_);
lean_dec_ref(v___y_5539_);
return v_res_5544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1(lean_object* v_00_u03b1_5545_, lean_object* v_constName_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_){
_start:
{
lean_object* v___x_5552_; 
v___x_5552_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___redArg(v_constName_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_);
return v___x_5552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5553_, lean_object* v_constName_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v_res_5560_; 
v_res_5560_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1(v_00_u03b1_5553_, v_constName_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_);
lean_dec(v___y_5558_);
lean_dec(v___y_5556_);
lean_dec_ref(v___y_5555_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_5561_, lean_object* v_ref_5562_, lean_object* v_constName_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_){
_start:
{
lean_object* v___x_5569_; 
v___x_5569_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___redArg(v_ref_5562_, v_constName_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_5570_, lean_object* v_ref_5571_, lean_object* v_constName_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_){
_start:
{
lean_object* v_res_5578_; 
v_res_5578_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2(v_00_u03b1_5570_, v_ref_5571_, v_constName_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_);
lean_dec(v___y_5576_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v_ref_5571_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_5579_, lean_object* v_ref_5580_, lean_object* v_msg_5581_, lean_object* v_declHint_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_){
_start:
{
lean_object* v___x_5588_; 
v___x_5588_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___redArg(v_ref_5580_, v_msg_5581_, v_declHint_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
return v___x_5588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5589_, lean_object* v_ref_5590_, lean_object* v_msg_5591_, lean_object* v_declHint_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_5589_, v_ref_5590_, v_msg_5591_, v_declHint_5592_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
lean_dec(v___y_5596_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
lean_dec(v_ref_5590_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_5599_, lean_object* v_declHint_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_){
_start:
{
lean_object* v___x_5606_; 
v___x_5606_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_5599_, v_declHint_5600_, v___y_5604_);
return v___x_5606_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_5607_, lean_object* v_declHint_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_){
_start:
{
lean_object* v_res_5614_; 
v_res_5614_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_5607_, v_declHint_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_);
lean_dec(v___y_5612_);
lean_dec_ref(v___y_5611_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
return v_res_5614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_5615_, lean_object* v_ref_5616_, lean_object* v_msg_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_){
_start:
{
lean_object* v___x_5623_; 
v___x_5623_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_ref_5616_, v_msg_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
return v___x_5623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5624_, lean_object* v_ref_5625_, lean_object* v_msg_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin_spec__1_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_5624_, v_ref_5625_, v_msg_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
lean_dec(v___y_5630_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v_ref_5625_);
return v_res_5632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5634_; lean_object* v___x_5635_; 
v___x_5634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_));
v___x_5635_ = l_Lean_stringToMessageData(v___x_5634_);
return v___x_5635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(lean_object* v_x_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v___x_5640_; lean_object* v___x_5641_; 
v___x_5640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_);
v___x_5641_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_5640_, v___y_5637_, v___y_5638_);
return v___x_5641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object* v_x_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v_res_5646_; 
v_res_5646_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(v_x_5642_, v___y_5643_, v___y_5644_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v_x_5642_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(lean_object* v___x_5648_, lean_object* v___x_5649_, lean_object* v___x_5650_, lean_object* v_declName_5651_, lean_object* v_stx_5652_, uint8_t v_x_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_){
_start:
{
lean_object* v___x_5657_; lean_object* v___x_5658_; lean_object* v___x_5659_; 
v___x_5657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_));
v___x_5658_ = l_Lean_Name_mkStr4(v___x_5648_, v___x_5649_, v___x_5650_, v___x_5657_);
v___x_5659_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(v_declName_5651_, v_stx_5652_, v___x_5658_, v___y_5654_, v___y_5655_);
return v___x_5659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object* v___x_5660_, lean_object* v___x_5661_, lean_object* v___x_5662_, lean_object* v_declName_5663_, lean_object* v_stx_5664_, lean_object* v_x_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_){
_start:
{
uint8_t v_x_151__boxed_5669_; lean_object* v_res_5670_; 
v_x_151__boxed_5669_ = lean_unbox(v_x_5665_);
v_res_5670_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(v___x_5660_, v___x_5661_, v___x_5662_, v_declName_5663_, v_stx_5664_, v_x_151__boxed_5669_, v___y_5666_, v___y_5667_);
lean_dec(v_stx_5664_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__32_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_));
v___x_5759_ = l_Lean_registerBuiltinAttribute(v___x_5758_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2____boxed(lean_object* v_a_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1616411946____hygCtx___hyg_2_();
return v_res_5761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_));
v___x_5764_ = l_Lean_stringToMessageData(v___x_5763_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(lean_object* v_x_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_){
_start:
{
lean_object* v___x_5769_; lean_object* v___x_5770_; 
v___x_5769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_);
v___x_5770_ = l_Lean_throwError___at___00Lean_Meta_Simp_registerSimproc_spec__0___redArg(v___x_5769_, v___y_5766_, v___y_5767_);
return v___x_5770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object* v_x_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_){
_start:
{
lean_object* v_res_5775_; 
v_res_5775_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(v_x_5771_, v___y_5772_, v___y_5773_);
lean_dec(v___y_5773_);
lean_dec_ref(v___y_5772_);
lean_dec(v_x_5771_);
return v_res_5775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(lean_object* v___x_5777_, lean_object* v___x_5778_, lean_object* v___x_5779_, lean_object* v_declName_5780_, lean_object* v_stx_5781_, uint8_t v_x_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_){
_start:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; 
v___x_5786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_));
v___x_5787_ = l_Lean_Name_mkStr4(v___x_5777_, v___x_5778_, v___x_5779_, v___x_5786_);
v___x_5788_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(v_declName_5780_, v_stx_5781_, v___x_5787_, v___y_5783_, v___y_5784_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object* v___x_5789_, lean_object* v___x_5790_, lean_object* v___x_5791_, lean_object* v_declName_5792_, lean_object* v_stx_5793_, lean_object* v_x_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_){
_start:
{
uint8_t v_x_151__boxed_5798_; lean_object* v_res_5799_; 
v_x_151__boxed_5798_ = lean_unbox(v_x_5794_);
v_res_5799_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___lam__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(v___x_5789_, v___x_5790_, v___x_5791_, v_declName_5792_, v_stx_5793_, v_x_151__boxed_5798_, v___y_5795_, v___y_5796_);
lean_dec(v_stx_5793_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5831_; lean_object* v___x_5832_; 
v___x_5831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn___closed__10_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_));
v___x_5832_ = l_Lean_registerBuiltinAttribute(v___x_5831_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2____boxed(lean_object* v_a_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_initFn_00___x40_Lean_Meta_Tactic_Simp_Simproc_1544969214____hygCtx___hyg_2_();
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg(lean_object* v_a_5835_){
_start:
{
lean_object* v___x_5837_; lean_object* v_env_5838_; lean_object* v___x_5839_; lean_object* v_ext_5840_; lean_object* v_toEnvExtension_5841_; lean_object* v_asyncMode_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; 
v___x_5837_ = lean_st_ref_get(v_a_5835_);
v_env_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc_ref(v_env_5838_);
lean_dec(v___x_5837_);
v___x_5839_ = l_Lean_Meta_Simp_simprocExtension;
v_ext_5840_ = lean_ctor_get(v___x_5839_, 1);
lean_inc_ref(v_ext_5840_);
v_toEnvExtension_5841_ = lean_ctor_get(v_ext_5840_, 0);
lean_inc_ref(v_toEnvExtension_5841_);
lean_dec_ref(v_ext_5840_);
v_asyncMode_5842_ = lean_ctor_get(v_toEnvExtension_5841_, 2);
lean_inc(v_asyncMode_5842_);
lean_dec_ref(v_toEnvExtension_5841_);
v___x_5843_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_5844_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5843_, v___x_5839_, v_env_5838_, v_asyncMode_5842_);
lean_dec(v_asyncMode_5842_);
v___x_5845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5844_);
return v___x_5845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg___boxed(lean_object* v_a_5846_, lean_object* v_a_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lean_Meta_Simp_getSimprocs___redArg(v_a_5846_);
lean_dec(v_a_5846_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object* v_a_5849_, lean_object* v_a_5850_){
_start:
{
lean_object* v___x_5852_; 
v___x_5852_ = l_Lean_Meta_Simp_getSimprocs___redArg(v_a_5850_);
return v___x_5852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_){
_start:
{
lean_object* v_res_5856_; 
v_res_5856_ = l_Lean_Meta_Simp_getSimprocs(v_a_5853_, v_a_5854_);
lean_dec(v_a_5854_);
lean_dec_ref(v_a_5853_);
return v_res_5856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object* v_a_5857_){
_start:
{
lean_object* v___x_5859_; lean_object* v_env_5860_; lean_object* v___x_5861_; lean_object* v_ext_5862_; lean_object* v_toEnvExtension_5863_; lean_object* v_asyncMode_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5859_ = lean_st_ref_get(v_a_5857_);
v_env_5860_ = lean_ctor_get(v___x_5859_, 0);
lean_inc_ref(v_env_5860_);
lean_dec(v___x_5859_);
v___x_5861_ = l_Lean_Meta_Simp_simprocSEvalExtension;
v_ext_5862_ = lean_ctor_get(v___x_5861_, 1);
lean_inc_ref(v_ext_5862_);
v_toEnvExtension_5863_ = lean_ctor_get(v_ext_5862_, 0);
lean_inc_ref(v_toEnvExtension_5863_);
lean_dec_ref(v_ext_5862_);
v_asyncMode_5864_ = lean_ctor_get(v_toEnvExtension_5863_, 2);
lean_inc(v_asyncMode_5864_);
lean_dec_ref(v_toEnvExtension_5863_);
v___x_5865_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_5866_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5865_, v___x_5861_, v_env_5860_, v_asyncMode_5864_);
lean_dec(v_asyncMode_5864_);
v___x_5867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5867_, 0, v___x_5866_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg___boxed(lean_object* v_a_5868_, lean_object* v_a_5869_){
_start:
{
lean_object* v_res_5870_; 
v_res_5870_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_5868_);
lean_dec(v_a_5868_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object* v_a_5871_, lean_object* v_a_5872_){
_start:
{
lean_object* v___x_5874_; 
v___x_5874_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_5872_);
return v___x_5874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object* v_a_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_){
_start:
{
lean_object* v_res_5878_; 
v_res_5878_ = l_Lean_Meta_Simp_getSEvalSimprocs(v_a_5875_, v_a_5876_);
lean_dec(v_a_5876_);
lean_dec_ref(v_a_5875_);
return v_res_5878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object* v_attrName_5879_){
_start:
{
lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5881_ = l_Lean_Meta_Simp_simprocExtensionMapRef;
v___x_5882_ = lean_st_ref_get(v___x_5881_);
v___x_5883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(v___x_5882_, v_attrName_5879_);
lean_dec(v___x_5882_);
v___x_5884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5884_, 0, v___x_5883_);
return v___x_5884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object* v_attrName_5885_, lean_object* v_a_5886_){
_start:
{
lean_object* v_res_5887_; 
v_res_5887_ = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(v_attrName_5885_);
lean_dec(v_attrName_5885_);
return v_res_5887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object* v_attrName_5894_){
_start:
{
lean_object* v___x_5895_; uint8_t v___x_5896_; 
v___x_5895_ = ((lean_object*)(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__0));
v___x_5896_ = lean_name_eq(v_attrName_5894_, v___x_5895_);
if (v___x_5896_ == 0)
{
lean_object* v___x_5897_; uint8_t v___x_5898_; 
v___x_5897_ = ((lean_object*)(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__2));
v___x_5898_ = lean_name_eq(v_attrName_5894_, v___x_5897_);
if (v___x_5898_ == 0)
{
lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5899_ = ((lean_object*)(l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName___closed__3));
v___x_5900_ = lean_name_append_after(v_attrName_5894_, v___x_5899_);
return v___x_5900_;
}
else
{
lean_object* v___x_5901_; 
lean_dec(v_attrName_5894_);
v___x_5901_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_302158981____hygCtx___hyg_2_));
return v___x_5901_;
}
}
else
{
lean_object* v___x_5902_; 
lean_dec(v_attrName_5894_);
v___x_5902_ = ((lean_object*)(l_Lean_Meta_Simp_initFn___closed__1_00___x40_Lean_Meta_Tactic_Simp_Simproc_3132623482____hygCtx___hyg_2_));
return v___x_5902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object* v_simprocAttrNameOrsimpAttrName_5903_){
_start:
{
lean_object* v___x_5905_; lean_object* v_a_5906_; 
v___x_5905_ = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(v_simprocAttrNameOrsimpAttrName_5903_);
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
lean_inc(v_a_5906_);
if (lean_obj_tag(v_a_5906_) == 1)
{
lean_dec_ref(v_a_5906_);
lean_dec(v_simprocAttrNameOrsimpAttrName_5903_);
return v___x_5905_;
}
else
{
lean_object* v___x_5907_; lean_object* v___x_5908_; 
lean_dec(v_a_5906_);
lean_dec_ref(v___x_5905_);
v___x_5907_ = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(v_simprocAttrNameOrsimpAttrName_5903_);
v___x_5908_ = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(v___x_5907_);
lean_dec(v___x_5907_);
return v___x_5908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f___boxed(lean_object* v_simprocAttrNameOrsimpAttrName_5909_, lean_object* v_a_5910_){
_start:
{
lean_object* v_res_5911_; 
v_res_5911_ = l_Lean_Meta_Simp_getSimprocExtension_x3f(v_simprocAttrNameOrsimpAttrName_5909_);
return v_res_5911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object* v_ext_5912_, lean_object* v_a_5913_){
_start:
{
lean_object* v___x_5915_; lean_object* v_ext_5916_; lean_object* v_toEnvExtension_5917_; lean_object* v_env_5918_; lean_object* v_asyncMode_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5915_ = lean_st_ref_get(v_a_5913_);
v_ext_5916_ = lean_ctor_get(v_ext_5912_, 1);
v_toEnvExtension_5917_ = lean_ctor_get(v_ext_5916_, 0);
v_env_5918_ = lean_ctor_get(v___x_5915_, 0);
lean_inc_ref(v_env_5918_);
lean_dec(v___x_5915_);
v_asyncMode_5919_ = lean_ctor_get(v_toEnvExtension_5917_, 2);
v___x_5920_ = l_Lean_Meta_Simp_instInhabitedSimprocs_default;
v___x_5921_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5920_, v_ext_5912_, v_env_5918_, v_asyncMode_5919_);
v___x_5922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5922_, 0, v___x_5921_);
return v___x_5922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg___boxed(lean_object* v_ext_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_){
_start:
{
lean_object* v_res_5926_; 
v_res_5926_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(v_ext_5923_, v_a_5924_);
lean_dec(v_a_5924_);
lean_dec_ref(v_ext_5923_);
return v_res_5926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object* v_ext_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_){
_start:
{
lean_object* v___x_5931_; 
v___x_5931_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(v_ext_5927_, v_a_5929_);
return v___x_5931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object* v_ext_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_, lean_object* v_a_5935_){
_start:
{
lean_object* v_res_5936_; 
v_res_5936_ = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(v_ext_5932_, v_a_5933_, v_a_5934_);
lean_dec(v_a_5934_);
lean_dec_ref(v_a_5933_);
lean_dec_ref(v_ext_5932_);
return v_res_5936_;
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
